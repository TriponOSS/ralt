/* native.c - P4 x86-64 backend (AT&T asm; `as` assembles, cc only links).
 * Pipeline per PLAN.md: typed AST -> flat TAC per fn -> linear-scan
 * regalloc -> deterministic AT&T text. No SSA.
 *
 * P4.1 slice: scalar ints (i8..u64), bool, str values (rodata pointers),
 * builtin prints, user + extern calls, if/while/return, compound assigns,
 * int<->int casts, len(str), str indexing, short-circuit logic, and the
 * trap protocol byte-exact with the C backend (E9001 overflow / E9002
 * str-index / E9003 div-zero; shared trap stub; -fast drops overflow guards
 * like the C path, keeping div-zero and narrow rechecks).
 *
 * Value model: every value is kept in its type's canonical 64-bit form
 * (sign/zero-extended). Binops compute in 64-bit, then width checks
 * reproduce the C backend's widen->guard->recheck semantics. Unsigned
 * div/mod reinterprets operands as signed, mirroring the C helpers.
 * Later slices: floats (P4.2), arrays/structs/enums/opt/result (P4.3).
 */
#include "common.h"
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ---------------- TAC ---------------- */

typedef enum {
    T_LI,        /* dst = imm (canonical for ty) */
    T_FLTI,      /* dst = rodata float const (imm carries the IEEE bits) */
    T_LEASTR,    /* dst = &rodata[strid] */
    T_MOV,       /* dst = a */
    T_BIN,       /* dst = a tok b   (+ - * / %) */
    T_CMP,       /* dst(bool) = a tok b (== != < > <= >=) */
    T_CAST,      /* dst = (ty)a   int<->int / float<->int / float<->float */
    T_NEG,       /* dst = -a      (signed int: trap; float: sign flip) */
    T_NOT,       /* dst = !a      (bool) */
    T_CALL,      /* dst? = callee(args..) */
    T_PRINT,     /* print_kind(a) */
    T_STRIDX,    /* dst(u8) = str(a)[idx(b)]  E9002 */
    T_RET,       /* return a? */
    T_BR,        /* jmp label */
    T_BCCZ,      /* if a == 0 goto label */
    T_BCCNZ,     /* if a != 0 goto label */
    T_LBL,       /* label: */
} TacOp;

typedef struct {
    TacOp op;
    int dst, a, b;           /* vreg ids; -1 = none */
    long long imm;
    const char *callee;      /* T_CALL */
    int is_extern, argc;
    int *argv;               /* T_CALL arg vregs */
    TokKind tok;             /* T_BIN op / T_CMP cond */
    Ty ty;                   /* result type: LI/BIN/CAST/CALL */
    const char *file;        /* trap site (BIN/NEG/STRIDX/f2i) */
    int line;
    int label;               /* T_LBL/T_BR/T_BCCZ/T_BCCNZ */
    int print_kind;          /* T_PRINT: 0=i32, 1=i64, 2=str, 3=f64 */
    int strid;               /* T_LEASTR */
    double flo, fhi;         /* f2i/f2u guard bounds (E9004) */
} Tac;

typedef struct {
    int id;
    Ty ty;
    int def, last;           /* TAC positions, inclusive */
    int crosses_call, crosses_div;
    int reg;                 /* phys reg index or -1 (spill) */
    int slot;                /* frame slot (1:1 with vreg id) */
    const char *varname;     /* locals carry their Tripon name */
} VReg;

typedef struct {
    Tac *t;
    int n, cap;
    VReg *v;
    int nv, vcap;
    int nlbl;
    FnDecl *fn;              /* owning decl (emission pairing) */
    const char *file;
} FnCg;

typedef struct {
    FnDecl **fns;            /* all fn decls (extern resolution) */
    int nfns;
    char **strs;             /* rodata blobs, file-wide, appearance order */
    int *strlens;
    int nstrs, strcap;
    bool fast;
} Ctx;

static void *xmalloc(size_t n) {
    void *p = malloc(n ? n : 1);
    if (!p) exit(1);
    return p;
}

static int strtab_add(Ctx *c, const char *text, size_t len) {
    if (c->nstrs == c->strcap) {
        c->strcap = c->strcap ? c->strcap * 2 : 16;
        c->strs = realloc(c->strs, sizeof(char *) * (size_t)c->strcap);
        c->strlens = realloc(c->strlens, sizeof(int) * (size_t)c->strcap);
        if (!c->strs || !c->strlens) exit(1);
    }
    char *copy = xmalloc(len + 1);
    memcpy(copy, text, len);
    copy[len] = 0;
    c->strs[c->nstrs] = copy;
    c->strlens[c->nstrs] = (int)len;
    return c->nstrs++;
}

static int tac_add(FnCg *f, Tac t) {
    if (f->n == f->cap) {
        f->cap = f->cap ? f->cap * 2 : 64;
        f->t = realloc(f->t, sizeof(Tac) * (size_t)f->cap);
        if (!f->t) exit(1);
    }
    f->t[f->n] = t;
    return f->n++;
}

static int vreg_new(FnCg *f, Ty ty) {
    if (f->nv == f->vcap) {
        f->vcap = f->vcap ? f->vcap * 2 : 64;
        f->v = realloc(f->v, sizeof(VReg) * (size_t)f->vcap);
        if (!f->v) exit(1);
    }
    VReg *r = &f->v[f->nv];
    memset(r, 0, sizeof *r);
    r->id = f->nv;
    r->ty = ty;
    r->reg = -1;
    r->def = -1;
    r->last = -1;
    r->slot = f->nv;
    return f->nv++;
}

static int lbl_new(FnCg *f) { return f->nlbl++; }

/* ---------------- type classification ---------------- */

static bool ty_signed(Ty t) {
    return t == TY_I8 || t == TY_I16 || t == TY_I32 || t == TY_I64 || t == TY_ISIZE;
}
static bool ty_unsig(Ty t) {
    return t == TY_U8 || t == TY_U16 || t == TY_U32 || t == TY_U64 || t == TY_USIZE;
}
static bool ty_ok(Ty t) {
    return ty_is_int(t) || t == TY_BOOL || t == TY_STR || t == TY_VOID ||
           t == TY_PTR8 || t == TY_UNSET || t == TY_STRUCT || t == TY_ARRAY ||
           t == TY_ENUM || t == TY_OPT || t == TY_RESULT;
}
static void reject_slice(void) {
    fprintf(stderr,
            "ralt native: construct not in the P4.1 slice yet "
            "(floats/arrays/structs/enums/opt/result/match arrive in later slices)\n");
    exit(1);
}
static void reject_ty(Ty t) {
    fprintf(stderr, "ralt native: type '%s' not in the P4.1 slice yet\n", ty_name(t));
    exit(1);
}

/* physical registers */
#define NREGS 12
#define NCALLEE 5
#define R_RAX 5
#define R_RDX 7
/* SysV int arg regs (indices into REGS): rdi rsi rdx rcx r8 r9 */
static const int ARGREG[6] = {9, 8, 7, 6, 10, 11};
#define R_R10 12   /* emitter-reserved shuffle temps, never allocated */
#define R_R11 13

/* ---------------- lowering ---------------- */

static Ty vreg_ty(FnCg *f, int v);
static int ev_expr(FnCg *f, Ctx *c, Expr *e);
static void ev_stmt(FnCg *f, Ctx *c, Stmt *s);

static int find_local(FnCg *f, const char *name) {
    for (int i = f->nv - 1; i >= 0; i--)
        if (f->v[i].varname && strcmp(f->v[i].varname, name) == 0) return i;
    return -1;
}

/* short-circuit && / ||: result 0/1 in a fresh bool vreg */
static int ev_logic(FnCg *f, Ctx *c, Expr *e, bool is_or) {
    int res = vreg_new(f, TY_BOOL);
    int a = ev_expr(f, c, e->lhs);
    if (is_or) {
        int ltrue = lbl_new(f), lend = lbl_new(f);
        tac_add(f, (Tac){.op = T_BCCNZ, .a = a, .label = ltrue});
        int b = ev_expr(f, c, e->rhs);
        tac_add(f, (Tac){.op = T_MOV, .dst = res, .a = b, .ty = TY_BOOL});
        tac_add(f, (Tac){.op = T_BR, .label = lend});
        tac_add(f, (Tac){.op = T_LBL, .label = ltrue});
        tac_add(f, (Tac){.op = T_LI, .dst = res, .imm = 1, .ty = TY_BOOL});
        tac_add(f, (Tac){.op = T_LBL, .label = lend});
    } else {
        int lfalse = lbl_new(f), lend = lbl_new(f);
        tac_add(f, (Tac){.op = T_BCCZ, .a = a, .label = lfalse});
        int b = ev_expr(f, c, e->rhs);
        tac_add(f, (Tac){.op = T_BCCZ, .a = b, .label = lfalse});
        tac_add(f, (Tac){.op = T_LI, .dst = res, .imm = 1, .ty = TY_BOOL});
        tac_add(f, (Tac){.op = T_BR, .label = lend});
        tac_add(f, (Tac){.op = T_LBL, .label = lfalse});
        tac_add(f, (Tac){.op = T_LI, .dst = res, .imm = 0, .ty = TY_BOOL});
        tac_add(f, (Tac){.op = T_LBL, .label = lend});
    }
    return res;
}

static int ev_cmp(FnCg *f, Ctx *c, Expr *e) {
    int a = ev_expr(f, c, e->lhs);
    int b = ev_expr(f, c, e->rhs);
    int d = vreg_new(f, TY_BOOL);
    tac_add(f, (Tac){.op = T_CMP, .dst = d, .a = a, .b = b, .tok = e->op,
                     .ty = TY_BOOL});
    return d;
}

static int ev_expr(FnCg *f, Ctx *c, Expr *e) {
    switch (e->kind) {
    case EX_INT: {
        Ty t = e->ty == TY_UNSET ? TY_I32 : e->ty;
        if (!ty_is_int(t)) reject_ty(t);
        int d = vreg_new(f, t);
        tac_add(f, (Tac){.op = T_LI, .dst = d, .imm = e->ival, .ty = t});
        return d;
    }
    case EX_FLOAT: {
        if (e->ty != TY_F64 && e->ty != TY_F32) reject_ty(e->ty);
        int d = vreg_new(f, e->ty);
        /* exact IEEE bits as a rodata blob: bit-identical constants, no
         * assembler-level decimal rounding */
        unsigned char bits[8];
        size_t nbits;
        if (e->ty == TY_F32) {
            float fv = (float)e->fval;
            memcpy(bits, &fv, 4);
            nbits = 4;
        } else {
            double dv = e->fval;
            memcpy(bits, &dv, 8);
            nbits = 8;
        }
        tac_add(f, (Tac){.op = T_FLTI, .dst = d, .ty = e->ty,
                         .imm = strtab_add(c, (const char *)bits, nbits)});
        return d;
    }
    case EX_BOOL: {
        int d = vreg_new(f, TY_BOOL);
        tac_add(f, (Tac){.op = T_LI, .dst = d, .imm = e->bval ? 1 : 0, .ty = TY_BOOL});
        return d;
    }
    case EX_STR: {
        int d = vreg_new(f, TY_STR);
        tac_add(f, (Tac){.op = T_LEASTR, .dst = d,
                         .imm = strtab_add(c, e->sval, e->slen), .ty = TY_STR});
        return d;
    }
    case EX_IDENT: {
        int v = find_local(f, e->sval);
        if (v < 0) {
            fprintf(stderr, "ralt native: unknown local '%s'\n", e->sval);
            exit(1);
        }
        return v;
    }
    case EX_CAST: {
        if (!ty_ok(e->ty)) reject_ty(e->ty);
        int s = ev_expr(f, c, e->operand);   /* evaluate exactly once */
        Ty st = e->operand->ty;
        if (e->ty == st) return s;
        bool src_f = ty_is_float(st), dst_f = ty_is_float(e->ty);
        if (src_f && dst_f) {
            /* f32<->f64: plain converts */
            int d = vreg_new(f, e->ty);
            tac_add(f, (Tac){.op = T_CAST, .dst = d, .a = s, .ty = e->ty});
            return d;
        }
        if (dst_f) {
            /* int -> float: plain convert (same as C) */
            int d = vreg_new(f, e->ty);
            tac_add(f, (Tac){.op = T_CAST, .dst = d, .a = s, .ty = e->ty});
            return d;
        }
        if (src_f) {
            /* float -> int: E9004 guard against the FINAL target bounds,
             * then truncate toward zero (mirrors tp_f2i_g / tp_f2u_g) */
            if (!ty_is_int(e->ty)) return s;   /* typecheck-gated identity */
            int d = vreg_new(f, e->ty);
            Tac t = {.op = T_CAST, .dst = d, .a = s, .ty = e->ty,
                     .file = e->span.file, .line = e->span.line};
            bool uns = ty_unsig(e->ty);
            switch (e->ty) {
            case TY_I8:  t.flo = uns ? 0 : -128.0; t.fhi = uns ? 256.0 : 128.0; break;
            case TY_I16: t.flo = uns ? 0 : -32768.0; t.fhi = uns ? 65536.0 : 32768.0; break;
            case TY_I32: t.flo = uns ? 0 : -2147483648.0; t.fhi = uns ? 4294967296.0 : 2147483648.0; break;
            case TY_U8:  t.flo = 0; t.fhi = 256.0; break;
            case TY_U16: t.flo = 0; t.fhi = 65536.0; break;
            case TY_U32: t.flo = 0; t.fhi = 4294967296.0; break;
            default:     t.flo = uns ? 0 : -9223372036854775808.0; t.fhi = uns ? 18446744073709551616.0 : 9223372036854775808.0; break;
            }
            tac_add(f, t);
            return d;
        }
        /* int -> int */
        if (!ty_is_int(e->ty) || !ty_is_int(st)) return s;
        if ((e->ty == TY_I64 && st == TY_ISIZE) || (e->ty == TY_ISIZE && st == TY_I64))
            return s;
        if ((e->ty == TY_U64 && st == TY_USIZE) || (e->ty == TY_USIZE && st == TY_U64))
            return s;
        int d = vreg_new(f, e->ty);
        tac_add(f, (Tac){.op = T_CAST, .dst = d, .a = s, .ty = e->ty});
        return d;
    }
    case EX_UN: {
        if (e->unop == UN_ADDR) reject_slice();
        int s = ev_expr(f, c, e->operand);
        if (e->unop == UN_NOT) {
            if (vreg_ty(f, s) != TY_BOOL) reject_slice();
            int d = vreg_new(f, TY_BOOL);
            tac_add(f, (Tac){.op = T_NOT, .dst = d, .a = s});
            return d;
        }
        int d = vreg_new(f, e->operand->ty);
        tac_add(f, (Tac){.op = T_NEG, .dst = d, .a = s, .ty = e->operand->ty,
                         .file = e->span.file, .line = e->span.line});
        return d;
    }
    case EX_BIN: {
        TokKind op = e->op;
        if (op == TK_AND) return ev_logic(f, c, e, false);
        if (op == TK_OR) return ev_logic(f, c, e, true);
        Ty bt = e->lhs->ty == TY_UNSET ? e->rhs->ty : e->lhs->ty;
        bool bf = ty_is_float(bt);
        if ((op == TK_EQ || op == TK_NE) && !bf) {
            if (e->lhs->ty == TY_STR || e->lhs->ty == TY_PTR8) {
                /* strcmp(a, b) == 0 */
                int a = ev_expr(f, c, e->lhs);
                int b = ev_expr(f, c, e->rhs);
                int *argv = xmalloc(sizeof(int) * 2);
                argv[0] = a;
                argv[1] = b;
                int sc = vreg_new(f, TY_I32);
                tac_add(f, (Tac){.op = T_CALL, .dst = sc, .callee = "strcmp",
                                 .is_extern = 1, .argv = argv, .argc = 2, .ty = TY_I32});
                int zero = vreg_new(f, TY_I32);
                tac_add(f, (Tac){.op = T_LI, .dst = zero, .imm = 0, .ty = TY_I32});
                int d = vreg_new(f, TY_BOOL);
                tac_add(f, (Tac){.op = T_CMP, .dst = d, .a = sc, .b = zero,
                                 .tok = op, .ty = TY_BOOL});
                return d;
            }
            return ev_cmp(f, c, e);
        }
        if (op == TK_LT || op == TK_GT || op == TK_LE || op == TK_GE)
            return ev_cmp(f, c, e);
        if (op == TK_PLUS || op == TK_MINUS || op == TK_STAR ||
            op == TK_SLASH || op == TK_PERCENT) {
            Ty t = e->lhs->ty == TY_UNSET ? e->rhs->ty : e->lhs->ty;
            if (ty_is_float(t)) {
                if (op == TK_PERCENT) reject_slice();   /* no fmod in Tripon */
                int a = ev_expr(f, c, e->lhs);
                int b = ev_expr(f, c, e->rhs);
                int d = vreg_new(f, t);
                tac_add(f, (Tac){.op = T_BIN, .dst = d, .a = a, .b = b, .tok = op,
                                 .ty = t});
                return d;
            }
            if (!ty_is_int(t)) reject_ty(t);
            int a = ev_expr(f, c, e->lhs);
            int b = ev_expr(f, c, e->rhs);
            int d = vreg_new(f, t);
            tac_add(f, (Tac){.op = T_BIN, .dst = d, .a = a, .b = b, .tok = op,
                             .ty = t, .file = e->span.file, .line = e->span.line});
            return d;
        }
        if (op == TK_POW) {
            if (!ty_is_float(bt)) reject_slice();
            int a = ev_expr(f, c, e->lhs);
            int b = ev_expr(f, c, e->rhs);
            int d = vreg_new(f, TY_F64);
            int *argv = xmalloc(sizeof(int) * 2);
            argv[0] = a;
            argv[1] = b;
            tac_add(f, (Tac){.op = T_CALL, .dst = d, .callee = "pow",
                             .is_extern = 1, .argv = argv, .argc = 2, .ty = TY_F64});
            return d;
        }
        reject_slice();   /* TK_POW (floats): P4.2 */
        return -1;
    }
    case EX_CALL: {
        if (strcmp(e->callee, "print_i32") == 0 || strcmp(e->callee, "print_i64") == 0 ||
            strcmp(e->callee, "print_f64") == 0 || strcmp(e->callee, "print_str") == 0) {
            int kind = strcmp(e->callee, "print_i32") == 0 ? 0
                     : strcmp(e->callee, "print_i64") == 0 ? 1
                     : strcmp(e->callee, "print_f64") == 0 ? 3 : 2;
            int a = ev_expr(f, c, e->args[0]);
            tac_add(f, (Tac){.op = T_PRINT, .a = a, .print_kind = kind});
            return -1;
        }
        if (strcmp(e->callee, "len") == 0) {
            if (e->args[0]->ty != TY_STR && e->args[0]->ty != TY_PTR8) reject_slice();
            int a = ev_expr(f, c, e->args[0]);
            int *argv = xmalloc(sizeof(int));
            argv[0] = a;
            int d = vreg_new(f, TY_I32);
            /* (int32_t)strlen(x): emitter canonicalizes rax per dst ty */
            tac_add(f, (Tac){.op = T_CALL, .dst = d, .callee = "strlen",
                             .is_extern = 1, .argv = argv, .argc = 1, .ty = TY_I32});
            return d;
        }
        FnDecl *fn = NULL;
        for (int i = 0; i < c->nfns; i++)
            if (strcmp(c->fns[i]->name, e->callee) == 0) { fn = c->fns[i]; break; }
        bool is_extern = fn ? fn->is_extern : true;
        if (fn && !fn->is_extern) {
            for (int i = 0; i < fn->nparams; i++)
                if (!ty_ok(fn->params[i].ty)) reject_ty(fn->params[i].ty);
            if (!ty_ok(fn->ret)) reject_ty(fn->ret);
        }
        if (e->nargs > 6) {
            fprintf(stderr, "ralt native: >6 scalar args unsupported in P4.1\n");
            exit(1);
        }
        if (e->ty != TY_VOID && !ty_ok(e->ty)) reject_ty(e->ty);
        int d = e->ty == TY_VOID ? -1 : vreg_new(f, e->ty);
        int *argv = xmalloc(sizeof(int) * (size_t)(e->nargs ? e->nargs : 1));
        for (int i = 0; i < e->nargs; i++) argv[i] = ev_expr(f, c, e->args[i]);
        tac_add(f, (Tac){.op = T_CALL, .dst = d, .callee = e->callee,
                         .is_extern = is_extern ? 1 : 0, .argv = argv,
                         .argc = e->nargs, .ty = e->ty});
        return d;
    }
    case EX_INDEX: {
        if (e->base->ty != TY_STR && e->base->ty != TY_PTR8) reject_slice();
        int s = ev_expr(f, c, e->base);
        int i = ev_expr(f, c, e->index);
        int d = vreg_new(f, TY_U8);
        tac_add(f, (Tac){.op = T_STRIDX, .dst = d, .a = s, .b = i,
                         .file = e->span.file, .line = e->span.line});
        return d;
    }
    default:
        reject_slice();
    }
    return -1;
}

static Ty vreg_ty(FnCg *f, int v) { return f->v[v].ty; }

static void ev_stmt(FnCg *f, Ctx *c, Stmt *s) {
    switch (s->kind) {
    case ST_LET: {
        if (!ty_ok(s->ty)) reject_ty(s->ty);
        int v = vreg_new(f, s->ty);
        f->v[v].varname = s->name;
        if (s->init) {
            int x = ev_expr(f, c, s->init);
            tac_add(f, (Tac){.op = T_MOV, .dst = v, .a = x, .ty = s->ty});
        } else if (s->ty == TY_STR) {
            /* zero value of str is the empty literal (never NULL) */
            tac_add(f, (Tac){.op = T_LEASTR, .dst = v,
                             .imm = strtab_add(c, "", 0), .ty = TY_STR});
        }
        break;
    }
    case ST_ASSIGN: {
        if (s->target->kind != EX_IDENT) reject_slice();   /* fields: P4.3 */
        int v = find_local(f, s->target->sval);
        if (v < 0) {
            fprintf(stderr, "ralt native: unknown local '%s'\n", s->target->sval);
            exit(1);
        }
        if (s->aop == TK_ASSIGN) {
            int x = ev_expr(f, c, s->value);
            tac_add(f, (Tac){.op = T_MOV, .dst = v, .a = x, .ty = f->v[v].ty});
        } else {
            TokKind op = s->aop == TK_ADDEQ ? TK_PLUS
                       : s->aop == TK_SUBEQ ? TK_MINUS
                       : s->aop == TK_MULEQ ? TK_STAR
                       : s->aop == TK_DIVEQ ? TK_SLASH : TK_PERCENT;
            int x = ev_expr(f, c, s->value);
            tac_add(f, (Tac){.op = T_BIN, .dst = v, .a = v, .b = x, .tok = op,
                             .ty = f->v[v].ty, .file = s->span.file, .line = s->span.line});
        }
        break;
    }
    case ST_RETURN: {
        if (s->value) {
            int x = ev_expr(f, c, s->value);
            tac_add(f, (Tac){.op = T_RET, .a = x});
        } else {
            tac_add(f, (Tac){.op = T_RET, .a = -1});
        }
        break;
    }
    case ST_IF: {
        int cond = ev_expr(f, c, s->cond);
        int lelse = lbl_new(f), lend = lbl_new(f);
        tac_add(f, (Tac){.op = T_BCCZ, .a = cond, .label = lelse});
        for (int i = 0; i < s->nbody; i++) ev_stmt(f, c, s->body[i]);
        tac_add(f, (Tac){.op = T_BR, .label = lend});
        tac_add(f, (Tac){.op = T_LBL, .label = lelse});
        if (s->els) ev_stmt(f, c, s->els);   /* recurse: else-if chains */
        tac_add(f, (Tac){.op = T_LBL, .label = lend});
        break;
    }
    case ST_WHILE: {
        int ltop = lbl_new(f), lend = lbl_new(f);
        tac_add(f, (Tac){.op = T_LBL, .label = ltop});
        int cond = ev_expr(f, c, s->cond);
        tac_add(f, (Tac){.op = T_BCCZ, .a = cond, .label = lend});
        for (int i = 0; i < s->nbody; i++) ev_stmt(f, c, s->body[i]);
        tac_add(f, (Tac){.op = T_BR, .label = ltop});
        tac_add(f, (Tac){.op = T_LBL, .label = lend});
        break;
    }
    case ST_EXPR:
        ev_expr(f, c, s->value);   /* value discarded (s->value, not cond) */
        break;
    case ST_BLOCK:
        for (int i = 0; i < s->nbody; i++) ev_stmt(f, c, s->body[i]);
        break;
    case ST_MATCH:
        reject_slice();
        break;
    }
}

/* ---------------- register allocation ---------------- */

static void fn_liveness(FnCg *f) {
    /* pass 1: full def/last intervals (final, not in-progress) */
    for (int p = 0; p < f->n; p++) {
        Tac *t = &f->t[p];
        int uses[10];
        int nu = 0;
        if (t->dst >= 0) uses[nu++] = t->dst;
        if (t->a >= 0) uses[nu++] = t->a;
        if (t->b >= 0) uses[nu++] = t->b;
        for (int i = 0; i < t->argc && nu < 10; i++) uses[nu++] = t->argv[i];
        for (int i = 0; i < nu; i++) {
            VReg *r = &f->v[uses[i]];
            if (r->def < 0) r->def = p;
            r->last = p;
        }
    }
    /* pass 2: clobber marking over the final intervals */
    for (int p = 0; p < f->n; p++) {
        Tac *t = &f->t[p];
        /* T_PRINT/T_STRIDX internally call libc (printf/strlen) and clobber
         * every caller-saved reg: they count as call points for liveness. */
        if (t->op == T_CALL || t->op == T_PRINT || t->op == T_STRIDX) {
            for (int v = 0; v < f->nv; v++) {
                VReg *r = &f->v[v];
                if (r->def < 0 || r->last < p) continue;
                bool is_arg = false;
                for (int i = 0; i < t->argc; i++)
                    if (t->argv[i] == v) is_arg = true;
                if (r->last > p || (r->last == p && !is_arg && t->dst != v))
                    r->crosses_call = 1;
            }
        }
        if (t->op == T_BIN && (t->tok == TK_SLASH || t->tok == TK_PERCENT)) {
            for (int v = 0; v < f->nv; v++) {
                VReg *r = &f->v[v];
                if (r->def < 0 || r->last < p) continue;
                if (r->last > p || t->dst != v) r->crosses_div = 1;
            }
        }
    }
}

static int vcmp(const void *x, const void *y) {
    const VReg *a = x, *b = y;
    if (a->def != b->def) return a->def - b->def;
    return a->id - b->id;
}

static void fn_alloc(FnCg *f) {
    VReg *order = xmalloc(sizeof(VReg) * (size_t)(f->nv ? f->nv : 1));
    memcpy(order, f->v, sizeof(VReg) * (size_t)f->nv);
    qsort(order, (size_t)f->nv, sizeof(VReg), vcmp);

    int taken[NREGS];
    for (int i = 0; i < NREGS; i++) taken[i] = -1;
    VReg **active = xmalloc(sizeof(VReg *) * (size_t)(f->nv ? f->nv : 1));
    int nactive = 0;

    for (int i = 0; i < f->nv; i++) {
        VReg *r = &order[i];
        /* expire intervals that ended before this def */
        for (int j = 0; j < nactive; j++) {
            if (active[j]->last < r->def) {
                if (active[j]->reg >= 0) taken[active[j]->reg] = -1;
                active[j] = active[--nactive];
                j--;
            }
        }
        int reg = -1;
        bool is_float = ty_is_float(r->ty);
        bool want_callee = r->crosses_call != 0;
        bool avoid_raxrdx = (r->crosses_call || r->crosses_div) != 0;
        /* floats always live in slots (SSE staging through xmm0/1 at emit) */
        for (int pass = 0; pass < 2 && reg < 0 && !is_float; pass++) {
            if (pass == 1 && want_callee) break;   /* crossers: callee or spill */
            bool callee_pass = pass == 0 ? want_callee : !want_callee;
            int lo = callee_pass ? 0 : NCALLEE, hi = callee_pass ? NCALLEE : NREGS;
            for (int g = lo; g < hi; g++) {
                if (taken[g] >= 0) continue;
                if (avoid_raxrdx && (g == R_RAX || g == R_RDX)) continue;
                reg = g;
                break;
            }
        }
        if (reg >= 0) {
            taken[reg] = r->id;
            r->reg = reg;
            active[nactive++] = r;
        }
    }
    /* copy allocations back by id (order[] is a sorted copy) */
    for (int i = 0; i < f->nv; i++) f->v[order[i].id].reg = order[i].reg;
    free(active);
    free(order);
    if (getenv("TP_DEBUG")) {
        for (int i = 0; i < f->nv; i++)
            fprintf(stderr, "v%-3d ty=%-4d def=%-3d last=%-3d cc=%d cd=%d reg=%d slot=%d %s\n",
                    f->v[i].id, (int)f->v[i].ty, f->v[i].def, f->v[i].last,
                    f->v[i].crosses_call, f->v[i].crosses_div, f->v[i].reg,
                    f->v[i].slot, f->v[i].varname ? f->v[i].varname : "");
    }
    if (getenv("TP_TAC")) {
        static const char *OPN[] = {"LI", "LEASTR", "MOV", "BIN", "CMP", "CAST",
            "NEG", "NOT", "CALL", "PRINT", "STRIDX", "RET", "BR", "BCCZ", "BCCNZ", "LBL"};
        for (int p = 0; p < f->n; p++) {
            Tac *t = &f->t[p];
            fprintf(stderr, "%3d %-7s d=%d a=%d b=%d", p, OPN[t->op], t->dst, t->a, t->b);
            if (t->op == T_BIN || t->op == T_CMP) fprintf(stderr, " tok=%d", (int)t->tok);
            if (t->op == T_CALL) fprintf(stderr, " %s ext=%d n=%d", t->callee, t->is_extern, t->argc);
            if (t->op == T_LI) fprintf(stderr, " imm=%lld", t->imm);
            if (t->op == T_LBL || t->op == T_BR) fprintf(stderr, " L%d", t->label);
            fputc('\n', stderr);
        }
    }
}

/* ---------------- asm emission ---------------- */

/* sub-register names by REGS index (r10/r11 appended at 12/13) */
static const char *W64[] = {"%rbx", "%r12", "%r13", "%r14", "%r15", "%rax",
    "%rcx", "%rdx", "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11"};
static const char *W32[] = {"%ebx", "%r12d", "%r13d", "%r14d", "%r15d", "%eax",
    "%ecx", "%edx", "%esi", "%edi", "%r8d", "%r9d", "%r10d", "%r11d"};
static const char *W16[] = {"%bx", "%r12w", "%r13w", "%r14w", "%r15w", "%ax",
    "%cx", "%dx", "%si", "%di", "%r8w", "%r9w", "%r10w", "%r11w"};
static const char *W8[] = {"%bl", "%r12b", "%r13b", "%r14b", "%r15b", "%al",
    "%cl", "%dl", "%sil", "%dil", "%r8b", "%r9b", "%r10b", "%r11b"};

typedef struct {
    FILE *o;
    Ctx *c;
    FnCg *f;
    /* trap sites (global numbering; per-fn slice emitted after its epilogue) */
    int *scodes, *sfiles, *slines, nsites, sitecap, sitebase;
    /* file-string table (file-wide) */
    char **ft;
    int nft, ftcap;
    int lblbase;             /* .LL%d base so labels stay unique per fn */
    int epiid, curepi;       /* .Lepi%d per fn */
} Em;

static char *locbuf(void);
static const char *tpname(const char *name);
static void emit_call(Em *e, Tac *t, const char *name);

static char *locbuf(void) {
    static char bufs[6][24];
    static int k = 0;
    char *b = bufs[k];
    k = (k + 1) % 6;
    return b;
}

static int filetab_get(Em *e, const char *file) {
    for (int i = 0; i < e->nft; i++)
        if (strcmp(e->ft[i], file) == 0) return i;
    if (e->nft == e->ftcap) {
        e->ftcap = e->ftcap ? e->ftcap * 2 : 8;
        e->ft = realloc(e->ft, sizeof(char *) * (size_t)e->ftcap);
        if (!e->ft) exit(1);
    }
    e->ft[e->nft] = (char *)file;
    return e->nft++;
}

static int site_get(Em *e, int code, const char *file, int line) {
    if (e->nsites == e->sitecap) {
        e->sitecap = e->sitecap ? e->sitecap * 2 : 16;
        e->scodes = realloc(e->scodes, sizeof(int) * (size_t)e->sitecap);
        e->sfiles = realloc(e->sfiles, sizeof(int) * (size_t)e->sitecap);
        e->slines = realloc(e->slines, sizeof(int) * (size_t)e->sitecap);
        if (!e->scodes || !e->sfiles || !e->slines) exit(1);
    }
    int n = e->nsites++;
    e->scodes[n] = code;
    e->sfiles[n] = filetab_get(e, file);
    e->slines[n] = line;
    return n;
}

static const char *slot_by_id(int slotid) {
    char *b = locbuf();
    snprintf(b, 24, "-%d(%%rbp)", 8 * (slotid + 1));
    return b;
}

static const char *slot_of(Em *e, int v) {
    return slot_by_id(e->f->v[v].slot);
}

static const char *loc_of(Em *e, int v) {
    if (e->f->v[v].reg >= 0) return W64[e->f->v[v].reg];
    return slot_of(e, v);
}

static void P(Em *e, const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    vfprintf(e->o, fmt, ap);
    va_end(ap);
    fputc('\n', e->o);
}

/* canonicalizing extend of src (reg idx or -1 for rax) into rax per ty */
static void extend_rax(Em *e, Ty t, int regidx, const char *memloc) {
    /* regidx >= 0: sub-width reg name; regidx < 0: memloc */
    const char *w8 = regidx >= 0 ? W8[regidx] : memloc;
    const char *w16 = regidx >= 0 ? W16[regidx] : memloc;
    const char *w32 = regidx >= 0 ? W32[regidx] : memloc;
    const char *w64 = regidx >= 0 ? W64[regidx] : memloc;
    switch (t) {
    case TY_I8:  P(e, "\tmovsbq %s, %%rax", w8); break;
    case TY_I16: P(e, "\tmovswq %s, %%rax", w16); break;
    case TY_I32: P(e, "\tmovslq %s, %%rax", w32); break;
    case TY_U8: case TY_BOOL: P(e, "\tmovzbq %s, %%rax", w8); break;
    case TY_U16: P(e, "\tmovzwq %s, %%rax", w16); break;
    case TY_U32: P(e, "\tmovl %s, %%eax", w32); break;   /* zero-extends */
    default:     P(e, "\tmovq %s, %%rax", w64); break;
    }
}

/* canonical store of rax into v (slot) */
static void store_rax(Em *e, int v) {
    if (e->f->v[v].reg >= 0)
        P(e, "\tmovq %%rax, %s", W64[e->f->v[v].reg]);
    else
        P(e, "\tmovq %%rax, %s", slot_of(e, v));
}

/* result already canonical in dst's reg (or rax if spilled): flush to slot */
static void flush_dst(Em *e, int v, int dstreg) {
    if (e->f->v[v].reg < 0)
        P(e, "\tmovq %s, %s", W64[dstreg], slot_of(e, v));
}

/* width range check on the value in dstreg (canonical iff in range) */
static void range_check(Em *e, int dstreg, Ty t, int site) {
    int r11 = R_R11;
    switch (t) {
    case TY_I8:  P(e, "\tmovsbq %s, %%r11", W8[dstreg]); break;
    case TY_I16: P(e, "\tmovswq %s, %%r11", W16[dstreg]); break;
    case TY_I32: P(e, "\tmovslq %s, %%r11", W32[dstreg]); break;
    case TY_U8:  P(e, "\tmovzbq %s, %%r11", W8[dstreg]); break;
    case TY_U16: P(e, "\tmovzwq %s, %%r11", W16[dstreg]); break;
    case TY_U32: P(e, "\tmovl %s, %%r11d", W32[dstreg]); break;
    default: return;   /* 64-bit types need no width check */
    }
    P(e, "\tcmpq %s, %s", W64[r11], W64[dstreg]);
    P(e, "\tjne .Lts%d", site);
}

static bool is_narrow(Ty t) {
    return t == TY_I8 || t == TY_I16 || t == TY_U8 || t == TY_U16;
}

static void emit_call(Em *e, Tac *t, const char *name);

static void emit_f2i(Em *e, Tac *t) {
    FnCg *f = e->f;
    Ty src = f->v[t->a].ty;
    bool is32 = src == TY_F32;
    const char *cm = is32 ? "ss" : "sd";
    bool uns = ty_unsig(t->ty);
    /* guard: v >= lo && v < hiex (exact powers of two; NaN fails both) */
    double lo = t->flo, hiex = t->fhi;
    unsigned char blob[16];
    size_t bw = is32 ? 4 : 8;
    memcpy(blob, &lo, bw);
    memcpy(blob + bw, &hiex, bw);
    int bid = strtab_add(e->c, (const char *)blob, (int)(bw * 2));
    P(e, "\tleaq .Lstr%d(%%rip), %%r10", bid);
    P(e, "\tmov%s %s, %%xmm0", cm, slot_by_id(f->v[t->a].slot));
    P(e, "\tucomis%s (%%r10), %%xmm0", cm);          /* v vs lo */
    int s1 = site_get(e, 9004, t->file, t->line);
    P(e, "\tjae 1f");                                /* v >= lo (NaN fails) */
    P(e, "\tjmp .Lts%d", s1);
    P(e, "1:");
    P(e, "\tucomis%s %d(%%r10), %%xmm0", cm, (int)bw); /* v vs hiex */
    int s2 = site_get(e, 9004, t->file, t->line);
    P(e, "\tjb 2f");                                 /* v < hiex */
    P(e, "\tjmp .Lts%d", s2);
    P(e, "2:");
    bool big64 = uns && (t->ty == TY_U64 || t->ty == TY_USIZE);
    if (big64) {
        /* v in [2^63, 2^64): convert halfwise then add the sign bit back */
        double two63 = 9223372036854775808.0;
        int b63 = strtab_add(e->c, (const char *)&two63, 8);
        P(e, "\tucomisd .Lstr%d(%%rip), %%xmm0", b63);
        P(e, "\tjb 5f");
        P(e, "\tsubsd .Lstr%d(%%rip), %%xmm0", b63);
        P(e, "\tcvttsd2si %%xmm0, %%rax");
        P(e, "\tmovabsq $-9223372036854775808, %%r11");
        P(e, "\taddq %%r11, %%rax");
        P(e, "\tjmp 6f");
        P(e, "5:");
        P(e, "\tcvttsd2si %%xmm0, %%rax");
        P(e, "6:");
    } else if (is32) {
        P(e, "\tcvttss2si %%xmm0, %%rax");
    } else {
        P(e, "\tcvttsd2si %%xmm0, %%rax");
    }
    /* truncation of an in-range value is already the target's canonical */
    if (t->ty == TY_U32)
        P(e, "\tmovl %%eax, %%eax");
    else if (t->ty == TY_I32)
        P(e, "\tmovslq %%eax, %%rax");
    store_rax(e, t->dst);
}

static void emit_bin(Em *e, Tac *t) {
    FnCg *f = e->f;
    bool is_div = t->tok == TK_SLASH || t->tok == TK_PERCENT;

    if (ty_is_float(t->ty)) {
        /* IEEE arithmetic, no guards (C parity); floats live in slots */
        const char *sfx = t->ty == TY_F64 ? "sd" : "ss";
        const char *aop = t->tok == TK_PLUS ? (t->ty == TY_F64 ? "addsd" : "addss")
                        : t->tok == TK_MINUS ? (t->ty == TY_F64 ? "subsd" : "subss")
                        : t->tok == TK_STAR ? (t->ty == TY_F64 ? "mulsd" : "mulss")
                        : (t->ty == TY_F64 ? "divsd" : "divss");
        P(e, "\tmov%s %s, %%xmm0", sfx, slot_by_id(f->v[t->a].slot));
        P(e, "\t%s %s, %%xmm0", aop, slot_by_id(f->v[t->b].slot));
        P(e, "\tmov%s %%xmm0, %s", sfx, slot_by_id(f->v[t->dst].slot));
        return;
    }

    int dstreg = f->v[t->dst].reg >= 0 ? f->v[t->dst].reg : R_RAX;
    bool uns = ty_unsig(t->ty);
    bool narrow = is_narrow(t->ty);
    bool width64 = t->ty == TY_I64 || t->ty == TY_U64 || t->ty == TY_ISIZE || t->ty == TY_USIZE;

    if (is_div) {
        /* zero guard always (mirrors tp_divz_g/divz64_g, kept under -fast) */
        int zs = site_get(e, 9003, t->file, t->line);
        P(e, "\tcmpq $0, %s", loc_of(e, t->b));
        P(e, "\tje .Lts%d", zs);
        if (width64) {
            P(e, "\tmovq %s, %%rax", loc_of(e, t->a));
            P(e, "\tcqto");
            P(e, "\tidivq %s", loc_of(e, t->b));   /* signed over bits: C parity */
        } else {
            /* 32-bit signed dance: parity with tp_divz_g incl. INT32_MIN/-1 */
            if (f->v[t->a].reg >= 0)
                P(e, "\tmovl %s, %%eax", W32[f->v[t->a].reg]);
            else
                P(e, "\tmovl %s, %%eax", slot_of(e, t->a));
            P(e, "\tcltd");
            if (f->v[t->b].reg >= 0)
                P(e, "\tidivl %s", W32[f->v[t->b].reg]);
            else
                P(e, "\tidivl %s", slot_of(e, t->b));
        }
        /* result: quotient %eax/%rax, remainder %edx/%rdx -> canonical rax */
        if (t->tok == TK_PERCENT)
            P(e, "\tmovq %%rdx, %%rax");
        switch (t->ty) {
        case TY_I32: P(e, "\tmovslq %%eax, %%rax"); break;
        case TY_U32: P(e, "\tmovl %%eax, %%eax"); break;
        default: break;   /* 64-bit: already canonical; narrow: fixed below */
        }
        if (narrow) {
            P(e, "\tmovslq %%eax, %%rax");
            int ns = site_get(e, 9001, t->file, t->line);
            /* direct imm bounds on the 32-bit result (all bounds fit imm32) */
            P(e, "\tmovq %%rax, %%r11");
            P(e, "\tcmpq %s, %%r11",
              t->ty == TY_I8 ? "$127" : t->ty == TY_I16 ? "$32767"
            : t->ty == TY_U8 ? "$255" : "$65535");
            P(e, "\tj%s .Lts%d", ty_signed(t->ty) ? "g" : "a", ns);
            if (ty_signed(t->ty)) {
                P(e, "\tcmpq %s, %%r11", t->ty == TY_I8 ? "$-128" : "$-32768");
                P(e, "\tjl .Lts%d", ns);
            } else {
                P(e, "\ttestq %%r11, %%r11");
                P(e, "\tjs .Lts%d", ns);
            }
        }
        /* div result lives in rax: materialize into dst (reg or slot) */
        if (f->v[t->dst].reg >= 0 && f->v[t->dst].reg != R_RAX)
            P(e, "\tmovq %%rax, %s", W64[f->v[t->dst].reg]);
        else if (f->v[t->dst].reg < 0)
            P(e, "\tmovq %%rax, %s", slot_by_id(f->v[t->dst].slot));
        return;
    }

    /* non-div: move a into dst, apply op, guard, width-check */
    const char *aop = t->tok == TK_PLUS ? "addq" : t->tok == TK_MINUS ? "subq" : "imulq";
    if (f->v[t->a].reg != dstreg || f->v[t->a].reg < 0) {
        if (f->v[t->a].reg == dstreg) {
            /* same reg, nothing to move */
        } else {
            P(e, "\tmovq %s, %s", loc_of(e, t->a), W64[dstreg]);
        }
    }
    P(e, "\t%s %s, %s", aop, loc_of(e, t->b), W64[dstreg]);

    if (!e->c->fast) {
        int site = site_get(e, 9001, t->file, t->line);
        if (t->tok == TK_PLUS || t->tok == TK_MINUS) {
            P(e, "\t%s .Lts%d", uns ? "jc" : "jo", site);
        } else {
            P(e, "\tjo .Lts%d", site);   /* imul OF covers signed + unsigned */
        }
    }
    /* width checks: narrow always (recheck even under -fast), i32/u32
     * unless -fast, 64-bit types guarded by the flag checks above */
    if (narrow || (!e->c->fast && (t->ty == TY_I32 || t->ty == TY_U32))) {
        int site = site_get(e, 9001, t->file, t->line);
        range_check(e, dstreg, t->ty, site);
    }
    flush_dst(e, t->dst, dstreg);
}

/* float compare: C NaN semantics (unordered -> only != is true).
 * ucomisd B, A flags A-B: EQ/NE/LT/LE need the PF dance; GT/GE are safe. */
static void emit_fcmp(Em *e, Tac *t) {
    FnCg *f = e->f;
    bool is32 = f->v[t->a].ty == TY_F32;
    P(e, "\tmov%s %s, %%xmm0", is32 ? "ss" : "sd", slot_by_id(f->v[t->a].slot));
    P(e, "\tucomis%s %s, %%xmm0", is32 ? "ss" : "sd", slot_by_id(f->v[t->b].slot));
    switch (t->tok) {
    case TK_EQ:
        P(e, "\tsete %%al");
        P(e, "\tsetnp %%cl");
        P(e, "\tandb %%cl, %%al");
        break;
    case TK_NE:
        P(e, "\tsetne %%al");
        P(e, "\tsetp %%cl");
        P(e, "\torb %%cl, %%al");
        break;
    case TK_LT:
        P(e, "\tsetb %%al");
        P(e, "\tsetnp %%cl");
        P(e, "\tandb %%cl, %%al");
        break;
    case TK_LE:
        P(e, "\tsetbe %%al");
        P(e, "\tsetnp %%cl");
        P(e, "\tandb %%cl, %%al");
        break;
    case TK_GT:
        P(e, "\tseta %%al");
        break;
    default:   /* TK_GE */
        P(e, "\tsetae %%al");
        break;
    }
    P(e, "\tmovzbq %%al, %%rax");
    store_rax(e, t->dst);
}

static void emit_cmp(Em *e, Tac *t) {
    FnCg *f = e->f;
    if (ty_is_float(f->v[t->a].ty)) {
        emit_fcmp(e, t);
        return;
    }
    /* flags of a-b: cmp loc(b), loc(a) with a in a reg */
    if (f->v[t->a].reg < 0) {
        P(e, "\tmovq %s, %%rax", slot_of(e, t->a));
        P(e, "\tcmpq %s, %%rax", loc_of(e, t->b));
        P(e, "\tset%s %%al",
          t->tok == TK_EQ ? "e" : t->tok == TK_NE ? "ne" :
          t->tok == TK_LT ? (ty_signed(f->v[t->a].ty) ? "l" : "b") :
          t->tok == TK_GT ? (ty_signed(f->v[t->a].ty) ? "g" : "a") :
          t->tok == TK_LE ? (ty_signed(f->v[t->a].ty) ? "le" : "be") :
                            (ty_signed(f->v[t->a].ty) ? "ge" : "ae"));
    } else {
        int ar = f->v[t->a].reg;
        P(e, "\tcmpq %s, %s", loc_of(e, t->b), W64[ar]);
        P(e, "\tset%s %%al",
          t->tok == TK_EQ ? "e" : t->tok == TK_NE ? "ne" :
          t->tok == TK_LT ? (ty_signed(f->v[t->a].ty) ? "l" : "b") :
          t->tok == TK_GT ? (ty_signed(f->v[t->a].ty) ? "g" : "a") :
          t->tok == TK_LE ? (ty_signed(f->v[t->a].ty) ? "le" : "be") :
                            (ty_signed(f->v[t->a].ty) ? "ge" : "ae"));
    }
    P(e, "\tmovzbq %%al, %%rax");
    store_rax(e, t->dst);
}

static void emit_call(Em *e, Tac *t, const char *name) {
    FnCg *f = e->f;
    enum { K_REG, K_SLOT, K_R10, K_R11, K_STACK };
    /* SysV: int args take GPRs in appearance order, float args take
     * xmm0..7 in appearance order - two independent queues. */
    int kind[6], loc[6];          /* int-subset machinery */
    int intv[6], nint = 0;
    for (int i = 0; i < t->argc; i++) {
        if (ty_is_float(f->v[t->argv[i]].ty)) continue;
        intv[nint++] = i;
    }
    for (int k = 0; k < nint; k++) {
        int i = intv[k];
        if (f->v[t->argv[i]].reg >= 0) {
            kind[k] = K_REG;
            loc[k] = f->v[t->argv[i]].reg;
        } else {
            kind[k] = K_SLOT;
            loc[k] = f->v[t->argv[i]].slot;
        }
    }
    /* phase 1 - decide: placing int arg k into GPR[k] destroys any later
     * int arg whose source still lives in that GPR; stash those out.
     * All indices here are positions in the INT arg queue. */
    int npush = 0, pushk[6], pushreg[6];
    bool r10_used = false, r11_used = false;
    for (int k = 0; k < nint; k++) {
        int target = ARGREG[k];
        for (int j = k + 1; j < nint; j++) {
            if (kind[j] == K_REG && loc[j] == target) {
                if (!r10_used) { kind[j] = K_R10; loc[j] = R_R10; r10_used = true; }
                else if (!r11_used) { kind[j] = K_R11; loc[j] = R_R11; r11_used = true; }
                else {
                    pushk[npush] = j;
                    pushreg[npush] = loc[j];
                    npush++;
                    kind[j] = K_STACK;
                    loc[j] = -1;
                }
            }
        }
    }
    /* phase 2 - emit (pad first so rsp stays 16-aligned at the call) */
    if (npush > 0 && npush % 2 == 1)
        P(e, "\tsubq $8, %%rsp");
    for (int i = 0; i < npush; i++)
        P(e, "\tpushq %s", W64[pushreg[i]]);
    for (int k = 0; k < nint; k++) {
        int target = ARGREG[k];
        if (kind[k] == K_REG && loc[k] == target) continue;
        switch (kind[k]) {
        case K_REG: case K_SLOT: {
            const char *from = kind[k] == K_REG ? W64[loc[k]] : slot_by_id(loc[k]);
            P(e, "\tmovq %s, %s", from, W64[target]);
            break;
        }
        case K_R10: P(e, "\tmovq %%r10, %s", W64[target]); break;
        case K_R11: P(e, "\tmovq %%r11, %s", W64[target]); break;
        default: break;   /* K_STACK: popped below */
        }
    }
    /* float args: slots -> xmm queue (appearance order) */
    int nxmm = 0;
    for (int i = 0; i < t->argc; i++) {
        Ty ty = f->v[t->argv[i]].ty;
        if (!ty_is_float(ty)) continue;
        P(e, "\tmov%s %s, %%xmm%d", ty == TY_F64 ? "sd" : "ss",
          slot_by_id(f->v[t->argv[i]].slot), nxmm++);
    }
    for (int i = npush - 1; i >= 0; i--)
        P(e, "\tpopq %s", W64[ARGREG[pushk[i]]]);
    if (npush > 0)
        P(e, "\taddq $%d, %%rsp", 8 * npush + (npush % 2 ? 8 : 0));
    if (t->is_extern && nxmm == 0)
        P(e, "\txorl %%eax, %%eax");   /* varargs: no vector args */
    if (t->is_extern && nxmm > 0)
        P(e, "\tmovl $%d, %%eax", nxmm); /* varargs: vector arg count */
    P(e, "\tcall %s", name);
    if (t->dst < 0)
        return;
    if (ty_is_float(t->ty)) {
        P(e, "\tmov%s %%xmm0, %s", t->ty == TY_F64 ? "sd" : "ss",
          slot_by_id(f->v[t->dst].slot));
    } else {
        extend_rax(e, t->ty, R_RAX, NULL);
        store_rax(e, t->dst);
    }
}

static void emit_tac(Em *e, Tac *t) {
    FnCg *f = e->f;
    switch (t->op) {
    case T_LI: {
        if (t->imm >= -2147483648LL && t->imm <= 2147483647LL) {
            if (f->v[t->dst].reg >= 0)
                P(e, "\tmovq $%lld, %s", t->imm, W64[f->v[t->dst].reg]);
            else
                P(e, "\tmovq $%lld, %s", t->imm, slot_by_id(f->v[t->dst].slot));
        } else {
            P(e, "\tmovabsq $%lld, %%rax", t->imm);
            store_rax(e, t->dst);
        }
        break;
    }
    case T_FLTI:
        /* float constant: 8-byte (f64) or 4-byte (f32) blob in rodata */
        P(e, "\tleaq .Lstr%d(%%rip), %%rax", (int)t->imm);
        if (t->ty == TY_F64) {
            P(e, "\tmovsd (%%rax), %%xmm0");
            P(e, "\tmovsd %%xmm0, %s", slot_by_id(f->v[t->dst].slot));
        } else {
            P(e, "\tmovss (%%rax), %%xmm0");
            P(e, "\tmovss %%xmm0, %s", slot_by_id(f->v[t->dst].slot));
        }
        break;
    case T_MOV: {
        if (f->v[t->dst].reg >= 0) {
            P(e, "\tmovq %s, %s", loc_of(e, t->a), W64[f->v[t->dst].reg]);
        } else if (f->v[t->a].reg >= 0) {
            P(e, "\tmovq %s, %s", W64[f->v[t->a].reg], slot_by_id(f->v[t->dst].slot));
        } else {
            P(e, "\tmovq %s, %%rax", slot_of(e, t->a));
            P(e, "\tmovq %%rax, %s", slot_by_id(f->v[t->dst].slot));
        }
        break;
    }
    case T_LEASTR:
        if (f->v[t->dst].reg >= 0)
            P(e, "\tleaq .Lstr%d(%%rip), %s", (int)t->imm, W64[f->v[t->dst].reg]);
        else {
            P(e, "\tleaq .Lstr%d(%%rip), %%rax", (int)t->imm);
            store_rax(e, t->dst);
        }
        break;
    case T_BIN:
        emit_bin(e, t);
        break;
    case T_CMP:
        emit_cmp(e, t);
        break;
    case T_CAST: {
        FnCg *f = e->f;
        Ty st = f->v[t->a].ty, dt = t->ty;
        if (ty_is_float(st)) {
            if (ty_is_float(dt)) {
                /* f32 <-> f64 */
                const char *scm = st == TY_F64 ? "sd" : "ss";
                const char *dcm = dt == TY_F64 ? "sd" : "ss";
                P(e, "\tmov%s %s, %%xmm0", scm, slot_of(e, t->a));
                if (scm != dcm) {
                    if (dt == TY_F64)
                        P(e, "\tcvtss2sd %%xmm0, %%xmm0");
                    else
                        P(e, "\tcvtsd2ss %%xmm0, %%xmm0");
                }
                P(e, "\tmov%s %%xmm0, %s", dcm, slot_by_id(f->v[t->dst].slot));
            } else {
                emit_f2i(e, t);   /* float -> int: E9004 guard + truncate */
            }
        } else if (ty_is_float(dt)) {
            /* int -> float */
            bool u32src = st == TY_U32;
            if (dt == TY_F64) {
                if (u32src) {
                    if (f->v[t->a].reg >= 0)
                        P(e, "\tmovl %s, %%eax", W32[f->v[t->a].reg]);
                    else
                        P(e, "\tmovl %s, %%eax", slot_of(e, t->a));
                    P(e, "\tcvtsi2sdq %%rax, %%xmm0");
                } else {
                    P(e, "\tcvtsi2sdq %s, %%xmm0", loc_of(e, t->a));
                }
                P(e, "\tmovsd %%xmm0, %s", slot_by_id(f->v[t->dst].slot));
            } else {
                if (u32src) {
                    /* exact via double: (float)(uint32) */
                    if (f->v[t->a].reg >= 0)
                        P(e, "\tmovl %s, %%eax", W32[f->v[t->a].reg]);
                    else
                        P(e, "\tmovl %s, %%eax", slot_of(e, t->a));
                    P(e, "\tcvtsi2sdq %%rax, %%xmm0");
                    P(e, "\tcvtsd2ss %%xmm0, %%xmm0");
                } else {
                    P(e, "\tcvtsi2ssq %s, %%xmm0", loc_of(e, t->a));
                }
                P(e, "\tmovss %%xmm0, %s", slot_by_id(f->v[t->dst].slot));
            }
        } else {
            extend_rax(e, t->ty, f->v[t->a].reg,
                       f->v[t->a].reg < 0 ? slot_of(e, t->a) : NULL);
            store_rax(e, t->dst);
        }
        break;
    }
    case T_NEG: {
        if (ty_is_float(t->ty)) {
            const char *cm = t->ty == TY_F64 ? "sd" : "ss";
            P(e, "\tmov%s %s, %%xmm0", cm, slot_of(e, t->a));
            P(e, "\txorpd %%xmm15, %%xmm15");
            P(e, "\tsub%s %%xmm0, %%xmm15", cm);   /* 0 - a */
            P(e, "\tmov%s %%xmm15, %s", cm, slot_by_id(f->v[t->dst].slot));
            break;
        }
        int dstreg = f->v[t->dst].reg >= 0 ? f->v[t->dst].reg : R_RAX;
        P(e, "\tmovq %s, %s", loc_of(e, t->a), W64[dstreg]);
        P(e, "\tnegq %s", W64[dstreg]);
        if (!e->c->fast) {
            int s = site_get(e, 9001, t->file, t->line);
            P(e, "\tjo .Lts%d", s);   /* INT64_MIN only; width check below */
        }
        /* canonical-form invariant: narrow/i32 negatives out of range must
         * trap (the C backend silently wraps here - documented divergence,
         * native is stricter). Skipped under -fast like every guard. */
        if (!e->c->fast && (is_narrow(t->ty) || t->ty == TY_I32)) {
            int s = site_get(e, 9001, t->file, t->line);
            range_check(e, dstreg, t->ty, s);
        }
        flush_dst(e, t->dst, dstreg);
        break;
    }
    case T_NOT:
        P(e, "\tcmpq $0, %s", loc_of(e, t->a));
        P(e, "\tsete %%al");
        P(e, "\tmovzbq %%al, %%rax");
        store_rax(e, t->dst);
        break;
    case T_PRINT:
        if (t->print_kind == 0) {
            P(e, "\tleaq .Lfmt_i32(%%rip), %%rdi");
            if (f->v[t->a].reg >= 0)
                P(e, "\tmovl %s, %%esi", W32[f->v[t->a].reg]);
            else
                P(e, "\tmovl %s, %%esi", slot_of(e, t->a));
            P(e, "\txorl %%eax, %%eax");
            P(e, "\tcall printf");
        } else if (t->print_kind == 1) {
            P(e, "\tleaq .Lfmt_i64(%%rip), %%rdi");
            P(e, "\tmovq %s, %%rsi", loc_of(e, t->a));
            P(e, "\txorl %%eax, %%eax");
            P(e, "\tcall printf");
        } else if (t->print_kind == 3) {
            P(e, "\tleaq .Lfmt_f64(%%rip), %%rdi");
            P(e, "\tmovsd %s, %%xmm0", slot_of(e, t->a));
            P(e, "\tmovl $1, %%eax");   /* one vector arg */
            P(e, "\tcall printf");
        } else {
            P(e, "\tleaq .Lfmt_str(%%rip), %%rdi");
            P(e, "\tmovq %s, %%rsi", loc_of(e, t->a));
            P(e, "\txorl %%eax, %%eax");
            P(e, "\tcall printf");
        }
        break;
    case T_STRIDX: {
        /* bounds: i < 0 || i >= strlen(str) -> E9002 (mirrors tp_strbounds_g) */
        int s1 = site_get(e, 9002, t->file, t->line);
        int s2 = site_get(e, 9002, t->file, t->line);
        P(e, "\tcmpq $0, %s", loc_of(e, t->b));
        P(e, "\tjl .Lts%d", s1);
        P(e, "\tmovq %s, %%rdi", loc_of(e, t->a));
        P(e, "\tcall strlen");
        P(e, "\tcmpq %%rax, %s", loc_of(e, t->b));
        P(e, "\tjge .Lts%d", s2);
        P(e, "\tmovq %s, %%r10", loc_of(e, t->a));
        P(e, "\tmovq %s, %%r11", loc_of(e, t->b));
        P(e, "\tmovzbq (%%r10,%%r11,1), %%rax");
        store_rax(e, t->dst);
        break;
    }
    case T_CALL:
        emit_call(e, t, t->is_extern ? t->callee : tpname(t->callee));
        break;
    case T_RET:
        if (t->a >= 0) {
            if (ty_is_float(t->ty))
                P(e, "\tmov%s %s, %%xmm0", t->ty == TY_F64 ? "sd" : "ss",
                  slot_of(e, t->a));
            else
                P(e, "\tmovq %s, %%rax", loc_of(e, t->a));
        }
        P(e, "\tjmp .Lepi%d", e->curepi);
        break;
    case T_BR:
        P(e, "\tjmp .LL%d", e->lblbase + t->label);
        break;
    case T_BCCZ:
        P(e, "\tcmpq $0, %s", loc_of(e, t->a));
        P(e, "\tje .LL%d", e->lblbase + t->label);
        break;
    case T_BCCNZ:
        P(e, "\tcmpq $0, %s", loc_of(e, t->a));
        P(e, "\tjne .LL%d", e->lblbase + t->label);
        break;
    case T_LBL:
        P(e, ".LL%d:", e->lblbase + t->label);
        break;
    }
}

static const char *tpname(const char *name) {
    static char b[64];
    if (strcmp(name, "main") == 0) return "main";
    snprintf(b, sizeof b, "tp_%s", name);
    return b;
}

static void emit_fn(Em *e, FnCg *f, FnDecl *fn) {
    e->f = f;
    const char *nm = tpname(fn->name);
    if (strcmp(fn->name, "main") == 0)
        P(e, "\t.globl %s", nm);
    P(e, "%s:", nm);
    P(e, "\tpushq %%rbp");
    P(e, "\tmovq %%rsp, %%rbp");
    int framesz = (8 * f->nv + 15) & ~15;
    /* params first: ints canonicalize through rax into their GPR or slot;
     * floats come in on the xmm queue and go straight to their slot */
    int gi = 0, xi = 0;
    for (int i = 0; i < fn->nparams; i++) {
        Ty pty = fn->params[i].ty;
        if (ty_is_float(pty)) {
            P(e, "\tmov%s %%xmm%d, %s", pty == TY_F64 ? "sd" : "ss", xi,
              slot_by_id(f->v[i].slot));
            xi++;
            continue;
        }
        extend_rax(e, pty, ARGREG[gi], NULL);
        if (f->v[i].reg >= 0 && f->v[i].reg != R_RAX)
            P(e, "\tmovq %%rax, %s", W64[f->v[i].reg]);
        else if (f->v[i].reg < 0)
            P(e, "\tmovq %%rax, %s", slot_by_id(f->v[i].slot));
        gi++;
    }
    if (f->nv > 0) {
        /* zero the frame with reserved regs only (r10/r11): allocated
         * scratch regs may already hold param values */
        P(e, "\tsubq $%d, %%rsp", framesz);
        P(e, "\tleaq -%d(%%rbp), %%r10", framesz);
        P(e, "\tmovq $%d, %%r11", f->nv);
        P(e, ".Lz%d:", e->epiid);
        P(e, "\tmovq $0, (%%r10)");
        P(e, "\taddq $8, %%r10");
        P(e, "\tsubq $1, %%r11");
        P(e, "\tjnz .Lz%d", e->epiid);
    }
    e->curepi = e->epiid++;
    for (int p = 0; p < f->n; p++)
        emit_tac(e, &f->t[p]);
    /* main(void) falls through like the C backend's implicit return 0 */
    if (strcmp(fn->name, "main") == 0 && fn->ret == TY_VOID)
        P(e, "\txorl %%eax, %%eax");
    P(e, ".Lepi%d:", e->curepi);
    P(e, "\tleave");
    P(e, "\tret");
    for (int s = e->sitebase; s < e->nsites; s++) {
        P(e, ".Lts%d:", s);
        P(e, "\tmovl $%d, %%edi", e->scodes[s]);
        P(e, "\tleaq .Lnm%d(%%rip), %%rsi", e->scodes[s]);
        P(e, "\tleaq .Lfl%d(%%rip), %%rdx", e->sfiles[s]);
        P(e, "\tmovl $%d, %%ecx", e->slines[s]);
        P(e, "\tjmp .Ltrap");
    }
    e->sitebase = e->nsites;
    e->lblbase += f->nlbl;
}

static void emit_blob(Em *e, const char *label, const char *bytes, int len) {
    P(e, "%s:", label);
    for (int i = 0; i < len; i += 16) {
        fprintf(e->o, "\t.byte ");
        for (int j = i; j < i + 16 && j < len; j++)
            fprintf(e->o, "%s%d", j > i ? ", " : "", (unsigned char)bytes[j]);
        fputc('\n', e->o);
    }
    P(e, "\t.byte 0");
}

void native_file(Arena *a, Decl **decls, int ndecls, const char *outpath, bool fast) {
    (void)a;
    Ctx c;
    memset(&c, 0, sizeof c);
    c.fast = fast;
    c.fns = xmalloc(sizeof(FnDecl *) * (size_t)(ndecls ? ndecls : 1));
    c.nfns = 0;
    for (int i = 0; i < ndecls; i++)
        if (decls[i]->kind == D_FN) c.fns[c.nfns++] = decls[i]->fn;

    /* one empty-string blob is guaranteed to exist (str zero value) */
    strtab_add(&c, "", 0);

    /* lower every non-extern fn, in decl order (deterministic) */
    FnCg **fcs = xmalloc(sizeof(FnCg *) * (size_t)(c.nfns ? c.nfns : 1));
    int nfc = 0;
    for (int i = 0; i < c.nfns; i++) {
        FnDecl *fn = c.fns[i];
        if (fn->is_extern || fn->nbody == 0) continue;
        for (int j = 0; j < fn->nparams; j++)
            if (!ty_ok(fn->params[j].ty)) reject_ty(fn->params[j].ty);
        if (!ty_ok(fn->ret)) reject_ty(fn->ret);
        FnCg *f = xmalloc(sizeof *f);
        memset(f, 0, sizeof *f);
        f->file = fn->span.file;
        f->fn = fn;
        for (int j = 0; j < fn->nparams; j++) {
            int v = vreg_new(f, fn->params[j].ty);
            f->v[v].varname = fn->params[j].name;
        }
        for (int j = 0; j < fn->nbody; j++)
            ev_stmt(f, &c, fn->body[j]);
        fn_liveness(f);
        fn_alloc(f);
        fcs[nfc++] = f;
    }

    FILE *out = fopen(outpath, "w");
    if (!out) {
        fprintf(stderr, "ralt: cannot write %s\n", outpath);
        exit(1);
    }
    Em em;
    memset(&em, 0, sizeof em);
    em.o = out;
    em.c = &c;

    P(&em, "\t.text");
    for (int i = 0; i < nfc; i++)
        emit_fn(&em, fcs[i], fcs[i]->fn);

    P(&em, "\t.section .rodata");
    for (int i = 0; i < c.nstrs; i++) {
        char lbl[24];
        snprintf(lbl, sizeof lbl, ".Lstr%d", i);
        emit_blob(&em, lbl, c.strs[i], c.strlens[i]);
    }
    P(&em, ".Lfmt_i32:");
    P(&em, "\t.asciz \"%%d\\n\"");
    P(&em, ".Lfmt_i64:");
    P(&em, "\t.asciz \"%%lld\\n\"");
    P(&em, ".Lfmt_str:");
    P(&em, "\t.asciz \"%%s\\n\"");
    P(&em, ".Ltrapfmt:");
    P(&em, "\t.asciz \"tripon trap E%%04d %%s at %%s:%%d\\n\"");
    P(&em, ".Lnm9001:");
    P(&em, "\t.asciz \"integer-overflow-trap\"");
    P(&em, ".Lnm9002:");
    P(&em, "\t.asciz \"index-out-of-bounds\"");
    P(&em, ".Lnm9003:");
    P(&em, "\t.asciz \"division-by-zero-trap\"");
    P(&em, ".Lnm9004:");
    P(&em, "\t.asciz \"cast-overflow-trap\"");
    P(&em, ".Lfmt_f64:");
    P(&em, "\t.asciz \"%%.2f\\n\"");
    for (int i = 0; i < em.nft; i++) {
        char lbl[24];
        snprintf(lbl, sizeof lbl, ".Lfl%d", i);
        emit_blob(&em, lbl, em.ft[i], (int)strlen(em.ft[i]));
    }

    P(&em, "\t.text");
    P(&em, ".Ltrap:");
    P(&em, "\tsubq $8, %%rsp");
    P(&em, "\tmovl %%ecx, %%r9d");
    P(&em, "\tmovq %%rdx, %%r8");
    P(&em, "\tmovq %%rsi, %%rcx");
    P(&em, "\tmovl %%edi, %%edx");
    P(&em, "\tleaq .Ltrapfmt(%%rip), %%rsi");
    P(&em, "\tmovq stderr(%%rip), %%rdi");
    P(&em, "\txorl %%eax, %%eax");
    P(&em, "\tcall fprintf");
    P(&em, "\tmovl $101, %%edi");
    P(&em, "\tcall exit");
    P(&em, "\t.section .note.GNU-stack,\"\",@progbits");
    fclose(out);
}

