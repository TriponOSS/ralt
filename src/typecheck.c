/* typecheck.c - the type-safety contract enforcement (spec section 3).
 * Strict: no implicit conversions of any kind, no null paths, errors as values. */
#include "common.h"

/* ---------------- anon opt/result enum registry (T3/T4 desugar) ---------------- */

#define ANON_MAX 128
static EnDecl *g_anons[ANON_MAX];
static int g_nanons = 0;

EnDecl *anon_find(const char *name) {
    for (int i = 0; i < g_nanons; i++)
        if (strcmp(g_anons[i]->name, name) == 0) return g_anons[i];
    return NULL;
}

EnDecl *anon_at(int i) { return i >= 0 && i < g_nanons ? g_anons[i] : NULL; }
int anon_count(void) { return g_nanons; }

/* fixed shape: variants[0] = some/ok (always 1 payload = T),
 * variants[1] = none (0 payloads) / err (1 payload = E). Tag ids:
 * some=0/none=1, ok=0/err=1 so match/`?` reuse the enum machinery as-is. */
EnDecl *anon_declare(const char *name, Payload *pls, int npl, Span sp) {
    EnDecl *ex = anon_find(name);
    if (ex) return ex;
    if (g_nanons == ANON_MAX) {
        diag(sp, E0202, SEV_ERROR, "too many distinct opt/result instantiations in this unit",
             "v0 caps anonymous opt/result shapes; refactor the payloads");
        return NULL;
    }
    EnDecl *en = calloc(1, sizeof *en);
    en->name = name;
    en->span = sp;
    en->variants = calloc(2, sizeof(Variant));
    en->nvariants = 2;
    en->variants[0].name = npl == 2 ? "ok" : "some";
    en->variants[0].span = sp;
    en->variants[1].name = npl == 2 ? "err" : "none";
    en->variants[1].span = sp;
    en->variants[0].npayloads = 1;
    en->variants[0].payloads = calloc(1, sizeof(Payload));
    en->variants[0].payloads[0] = pls[0];
    en->variants[1].npayloads = npl == 2 ? 1 : 0;
    if (npl == 2) {
        en->variants[1].payloads = calloc(1, sizeof(Payload));
        en->variants[1].payloads[0] = pls[1];
    }
    g_anons[g_nanons++] = en;
    return en;
}

/* ---------------- symbol tables ---------------- */

typedef struct {
    const char *name;
    Ty ty;
    const char *tname;      /* struct/enum type name when ty is one */
    bool is_const;
    Span span;
} Local;

typedef struct Scope {
    Local *locals;
    int nlocals;
    struct Scope *parent;
} Scope;

typedef struct {
    Arena *a;
    Scope *scopes;
    FnDecl **funcs;
    int nfuncs;
    StDecl **sts;
    int nsts;
    EnDecl **ens;
    int nens;
    FnDecl *cur_fn;
    Ty exp_ty;          /* expected-type context for bare ctor resolution */
    const char *exp_tn;
    int spread_pos;     /* `?` allowed: let init/expr stmt/assign/return */
} Ctx;

typedef enum { FOUND = 0, NOTFOUND } Res;

static Res scope_insert(Ctx *c, const char *name, Ty ty, const char *tname,
                        bool is_const, Span sp) {
    if (!c->scopes) {
        c->scopes = (Scope *)arena_zalloc(c->a, sizeof(Scope));
        c->scopes->parent = NULL;
    }
    /* shadowing check across all open scopes (warn only, later: config) */
    for (Scope *f = c->scopes; f; f = f->parent)
        for (int i = 0; i < f->nlocals; i++)
            if (strcmp(f->locals[i].name, name) == 0) {
                char msg[200];
                snprintf(msg, sizeof msg, "'%s' shadows an existing binding", name);
                diag(sp, E0603, SEV_WARN, msg, "rename the inner binding or drop shadowing intent");
                goto done;
            }
done: ;
    Local *na = arena_alloc(c->a, sizeof(Local) * (size_t)(c->scopes->nlocals + 1));
    if (c->scopes->nlocals)
        memcpy(na, c->scopes->locals, sizeof(Local) * (size_t)c->scopes->nlocals);
    na[c->scopes->nlocals] = (Local){name, ty, tname, is_const, sp};
    c->scopes->locals = na;
    c->scopes->nlocals++;
    return FOUND;
}

/* ---------------- built-in stdlib prelude (tier core) ---------------- */

typedef struct {
    const char *name;
    Ty ret;
    int argc;
    Ty args[4];
} Builtin;

static const Builtin BUILTINS[] = {
    /* Tripon stdlib prelude v0, tier core, always available, no import */
    {"print_i32", TY_VOID, 1, {TY_I32, TY_UNSET, TY_UNSET, TY_UNSET}},
    {"print_i64", TY_VOID, 1, {TY_I64, TY_UNSET, TY_UNSET, TY_UNSET}},
    {"print_f64", TY_VOID, 1, {TY_F64, TY_UNSET, TY_UNSET, TY_UNSET}},
    {"print_str", TY_VOID, 1, {TY_STR, TY_UNSET, TY_UNSET, TY_UNSET}},
    {"len",       TY_I32, 1, {TY_STR, TY_UNSET, TY_UNSET, TY_UNSET}},
    /* GUI builtins (Linux/GTK backend) */
};

static bool builtin_info(const char *name, int *ret, int *argc, Ty *args) {
    for (size_t i = 0; i < sizeof BUILTINS / sizeof BUILTINS[0]; i++) {
        if (strcmp(BUILTINS[i].name, name) == 0) {
            *ret = BUILTINS[i].ret;
            *argc = BUILTINS[i].argc;
            for (int k = 0; k < BUILTINS[i].argc && k < 4; k++) args[k] = BUILTINS[i].args[k];
            return true;
        }
    }
    return false;
}

/* ---------------- fn table prepass ---------------- */

static void prepass_fns(Ctx *c, Decl **decls, int ndecls) {
    c->funcs = arena_zalloc(c->a, sizeof(FnDecl *) * (size_t)(ndecls ? ndecls : 1));
    for (int i = 0; i < ndecls; i++) {
        if (decls[i]->kind == D_FN) {
            /* duplicate check */
            for (int j = 0; j < i && j < c->nfuncs; j++)
                if (strcmp(c->funcs[j]->name, decls[i]->fn->name) == 0 && !decls[i]->fn->is_extern) {
                    char msg[180];
                    snprintf(msg, sizeof msg, "function '%s' is already defined", decls[i]->fn->name);
                    diag(decls[i]->fn->span, E0201, SEV_ERROR, msg,
                         "one definition per name in a compilation unit");
                }
            c->funcs[c->nfuncs++] = decls[i]->fn;
        }
    }
}

static FnDecl *find_fn(Ctx *c, const char *name) {
    for (int i = 0; i < c->nfuncs; i++)
        if (strcmp(c->funcs[i]->name, name) == 0) return c->funcs[i];
    return NULL;
}

static StDecl *find_struct(Ctx *c, const char *name) {
    for (int i = 0; i < c->nsts; i++)
        if (strcmp(c->sts[i]->name, name) == 0) return c->sts[i];
    return NULL;
}

static EnDecl *find_enum(Ctx *c, const char *name) {
    for (int i = 0; i < c->nens; i++)
        if (strcmp(c->ens[i]->name, name) == 0) return c->ens[i];
    return anon_find(name);     /* built-in opt/result shapes */
}

/* ---------------- type decl prepass (in source order) ---------------- */

/* resolve a nominal type name against what has been declared so far */
static Ty resolve_tname(Ctx *c, const char *name, Span sp) {
    if (!name) return TY_UNSET;
    /* field context: names resolve against earlier decls; enum payloads too */
    for (int i = 0; i < c->nsts; i++)
        if (strcmp(c->sts[i]->name, name) == 0) return TY_STRUCT;
    for (int i = 0; i < c->nens; i++)
        if (strcmp(c->ens[i]->name, name) == 0) return TY_ENUM;
    diag(sp, E0101, SEV_ERROR, "unknown type name",
         "builtins: i8 i16 i32 i64 u8 u16 u32 u64 isize usize f32 f64 bool str; "
         "struct and enum types must be declared before use");
    return TY_UNSET;
}

static void resolve_array(Ctx *c, const char *name, Span sp) {
    ArrayInfo *ai = array_find(name);
    if (!ai) return;
    if (ai->elem_ty == TY_TYPEDEF)
        ai->elem_ty = resolve_tname(c, ai->elem_tname, sp);
    else if (ai->elem_ty == TY_ARRAY)
        resolve_array(c, ai->elem_tname, sp);
}

static void prepass_types(Ctx *c, Decl **decls, int ndecls) {
    c->sts = arena_zalloc(c->a, sizeof(StDecl *) * (size_t)(ndecls ? ndecls : 1));
    c->ens = arena_zalloc(c->a, sizeof(EnDecl *) * (size_t)(ndecls ? ndecls : 1));
    for (int i = 0; i < ndecls; i++) {
        if (decls[i]->kind == D_STRUCT) {
            StDecl *st = decls[i]->st;
            for (int j = 0; j < c->nsts; j++)
                if (strcmp(c->sts[j]->name, st->name) == 0) {
                    char msg[200];
                    snprintf(msg, sizeof msg, "type '%s' is already declared", st->name);
                    diag(st->span, E0201, SEV_ERROR, msg, "one definition per name");
                }
            /* fields first (no recursion: earlier decls only), then register */
            for (int f = 0; f < st->nfields; f++) {
                StField *fl = &st->fields[f];
                if (fl->ty == TY_TYPEDEF) fl->ty = resolve_tname(c, fl->tname, fl->span);
                else if (fl->ty == TY_ARRAY) resolve_array(c, fl->tname, fl->span);
            }
            c->sts[c->nsts++] = st;
        } else if (decls[i]->kind == D_ENUM) {
            EnDecl *en = decls[i]->en;
            for (int j = 0; j < c->nens; j++)
                if (strcmp(c->ens[j]->name, en->name) == 0) {
                    char msg[200];
                    snprintf(msg, sizeof msg, "type '%s' is already declared", en->name);
                    diag(en->span, E0201, SEV_ERROR, msg, "one definition per name");
                }
            for (int v = 0; v < en->nvariants; v++)
                for (int k = 0; k < en->variants[v].npayloads; k++) {
                    Payload *pl = &en->variants[v].payloads[k];
                    if (pl->ty == TY_TYPEDEF) pl->ty = resolve_tname(c, pl->tname, pl->span);
                    else if (pl->ty == TY_ARRAY) {
                        resolve_array(c, pl->tname, pl->span);
                        diag(pl->span, E0202, SEV_ERROR,
                             "arrays are not allowed in enum payloads in v0",
                             "carry the array in a struct or keep it as a local");
                    }
                }
            c->ens[c->nens++] = en;
        }
    }
    /* local array annotations resolve against all declared types */
    for (int i = 0; i < array_count(); i++) {
        ArrayInfo *ai = array_at(i);
        resolve_array(c, ai->name, ai->span);
    }
    /* fn signatures may reference any declared type in the file */
    for (int i = 0; i < ndecls; i++) {
        if (decls[i]->kind != D_FN) continue;
        FnDecl *fn = decls[i]->fn;
        for (int k = 0; k < fn->nparams; k++) {
            if (fn->params[k].ty == TY_TYPEDEF)
                fn->params[k].ty = resolve_tname(c, fn->params[k].tname, fn->params[k].span);
            if (fn->params[k].ty == TY_ARRAY)
                diag(fn->params[k].span, E0202, SEV_ERROR,
                     "arrays are local-only in v0 (no array parameters)",
                     "pass a struct wrapper or index the array in the caller");
        }
        if (fn->ret == TY_TYPEDEF)
            fn->ret = resolve_tname(c, fn->retname, fn->span);
        if (fn->ret == TY_ARRAY)
            diag(fn->span, E0202, SEV_ERROR,
                 "arrays are local-only in v0 (no array returns)",
                 "return a struct wrapper or fill a caller-owned array");
    }
    /* anon opt/result payloads resolve like enum payloads; parsed v0 surface
     * violations (nesting, str-in-opt, void) already carry their parse diag */
    for (int i = 0; i < g_nanons; i++) {
        bool is_opt = g_anons[i]->variants[1].npayloads == 0;
        for (int v = 0; v < g_anons[i]->nvariants; v++)
            for (int k = 0; k < g_anons[i]->variants[v].npayloads; k++) {
                Payload *pl = &g_anons[i]->variants[v].payloads[k];
                if (pl->ty == TY_TYPEDEF)
                    pl->ty = resolve_tname(c, pl->tname, pl->span);
                if (pl->ty == TY_ARRAY) {
                    diag(pl->span, E0202, SEV_ERROR,
                         "arrays are not allowed in opt/result payloads in v0",
                         "wrap the array in a struct or keep it as a local");
                    continue;
                }
                if (pl->ty == TY_UNSET || pl->ty == TY_VOID ||
                    (pl->ty == TY_STR && is_opt) ||
                    pl->ty == TY_OPT || pl->ty == TY_RESULT) continue;
                if (pl->ty == TY_ENUM) {
                    char msg[220];
                    snprintf(msg, sizeof msg,
                             "opt/result payloads v0 take a scalar, str, or struct, not '%s'",
                             pl->tname ? pl->tname : "?");
                    diag(pl->span, E0202, SEV_ERROR, msg, "match enums at the use site instead");
                }
            }
    }
}

/* struct/enum-aware display name and equality */
static const char *ty_disp(Ty t, const char *tnm);

/* one opt/result display: "opt<i32>" / "result<i32, str>" from the anon name */
static void tx_disp(char *buf, size_t n, Ty t, const char *tnm) {
    EnDecl *en = tnm ? anon_find(tnm) : NULL;
    if (!en) { snprintf(buf, n, "%s", tnm ? tnm : ty_name(t)); return; }
    const char *pay0 = en->variants[0].npayloads == 1
        ? ty_disp(en->variants[0].payloads[0].ty, en->variants[0].payloads[0].tname) : "?";
    if (en->variants[1].npayloads == 0)
        snprintf(buf, n, "opt<%s>", pay0);
    else snprintf(buf, n, "result<%s, %s>", pay0,
                  ty_disp(en->variants[1].payloads[0].ty, en->variants[1].payloads[0].tname));
}

static const char *ty_disp(Ty t, const char *tnm) {
    if (t == TY_ARRAY) {
        static char abufs[4][160];
        static int arot = 0;
        char *b = abufs[arot++ % 4];
        ArrayInfo *ai = array_find(tnm);
        if (!ai) snprintf(b, sizeof abufs[0], "[?]?");
        else snprintf(b, sizeof abufs[0], "[%d]%s", ai->len,
                      ty_disp(ai->elem_ty, ai->elem_tname));
        return b;
    }
    if (t == TY_OPT || t == TY_RESULT) {
        static char bufs[4][96];
        static int rot = 0;
        char *b = bufs[rot++ % 4];
        tx_disp(b, sizeof bufs[0], t, tnm);
        return b;
    }
    if (t == TY_STRUCT || t == TY_ENUM || t == TY_TYPEDEF) return tnm ? tnm : "composite";
    return ty_name(t);
}

static bool ty_same(Ty a, const char *an, Ty b, const char *bn) {
    if (a != b) return false;
    if (a == TY_STRUCT || a == TY_ENUM || a == TY_TYPEDEF ||
        a == TY_OPT || a == TY_RESULT || a == TY_ARRAY || a == TY_FN)
        return an && bn && strcmp(an, bn) == 0;
    return true;
}

/* the extern "C" fence (T7) is the one place pointer/text types meet:
 * *i8 char* values pass into str positions and literals pass into *i8 */
static bool ty_fence_ok(Ty a, Ty b) {
    return (a == TY_PTR8 && b == TY_STR) || (a == TY_STR && b == TY_PTR8);
}

/* ---------------- expression typing ---------------- */

/* numeric literals are untyped-until-context: in bin ops and assigns they
 * adopt the partner's numeric type when representable (not an implicit
 * conversion - the literal type IS context). Returns TY_UNSET if the literal
 * cannot take the partner's type (caller reports E0202). */
static Ty lit_adopt(Expr *lit, Ty partner) {
    long long v = lit->ival;
    switch (partner) {
    case TY_I8:  if (v >= -128 && v <= 127) return TY_I8; break;
    case TY_I16: if (v >= INT16_MIN && v <= INT16_MAX) return TY_I16; break;
    case TY_I32: if (v >= INT32_MIN && v <= INT32_MAX) return TY_I32; break;
    case TY_I64: case TY_ISIZE: return TY_I64;
    case TY_U8:  if (v >= 0 && v <= 255) return TY_U8; break;
    case TY_U16: if (v >= 0 && v <= 65535) return TY_U16; break;
    case TY_U32: if (v >= 0 && v <= 4294967295) return TY_U32; break;
    case TY_U64: case TY_USIZE: if (v >= 0) return TY_U64; break;
    case TY_F32: case TY_F64: return partner;
    default: break;
    }
    return TY_UNSET;
}

/* integer literal index: plain int or a negated int literal */
static bool idx_lit(Expr *e, long long *v) {
    if (e->kind == EX_INT) { *v = e->ival; return true; }
    if (e->kind == EX_UN && e->unop == UN_NEG && e->operand &&
        e->operand->kind == EX_INT) {
        *v = -e->operand->ival;
        return true;
    }
    return false;
}

/* -------- expected-type context + bare ctor plumbing (T3/T4) -------- */

static Ty tc_expr(Ctx *c, Expr *e);

/* tc_expr with the expected type for bare same/none/ok/err construction */
static Ty tc_expr_w(Ctx *c, Expr *e, Ty want, const char *wtn) {
    Ty sw = c->exp_ty;
    const char *sn = c->exp_tn;
    c->exp_ty = want;
    c->exp_tn = wtn;
    Ty t = tc_expr(c, e);
    c->exp_ty = sw;
    c->exp_tn = sn;
    return t;
}

/* bare opt/result ctors: convert the call/ident into the anon enum's EX_VARIANT
 * so later passes reuse the plain variant machinery unchanged. */
static Ty tc_ctor(Ctx *c, Expr *e, const char *vname) {
    Span sp = e->span;
    Ty wty = c->exp_ty;
    const char *wtn = c->exp_tn;

    if (wty != TY_OPT && wty != TY_RESULT) {
        /* no ctx: only some(x) carries enough info to infer one */
        if (vname[0] == 'n') {
            diag(sp, E0202, SEV_ERROR, "bare 'none' has no type context",
                 "declare the shape first: let x: opt<i32> = none;");
            e->ty = TY_UNSET;
            return TY_UNSET;
        }
        if (vname[0] != 's') {   /* ok/err never infer: result needs both payload types */
            diag(sp, E0202, SEV_ERROR, "'ok(v)'/'err(e)' have no type context to aim at",
                 "declare the shape first: let r: result<i32, str> = ok(v);");
            for (int k = 0; k < e->nargs; k++) tc_expr(c, e->args[k]);
            e->ty = TY_UNSET;
            return TY_UNSET;
        }
        if (e->nargs != 1) {
            diag(sp, E0202, SEV_ERROR, "'some' in no context needs exactly one payload value",
                 "declare the shape first: let x: opt<i32> = some(5);");
            for (int k = 0; k < e->nargs; k++) tc_expr(c, e->args[k]);
            e->ty = TY_UNSET;
            return TY_UNSET;
        }
        Ty at = tc_expr(c, e->args[0]);
        if (at == TY_UNSET) { e->ty = TY_UNSET; return TY_UNSET; }
        if (at == TY_OPT || at == TY_RESULT) {
            diag(e->args[0]->span, E0202, SEV_ERROR, "opt cannot nest v0 (same for result)",
                 "flatten the shape: carry nest-shaped data in a struct");
            e->ty = TY_UNSET;
            return TY_UNSET;
        }
        if (!(ty_is_num(at) || at == TY_BOOL || at == TY_STRUCT || at == TY_STR)) {
            diag(e->args[0]->span, E0202, SEV_ERROR,
                 "cannot infer an opt payload from this value",
                 "declare the target type, e.g. let x: opt<i32> = some(v);");
            e->ty = TY_UNSET;
            return TY_UNSET;
        }
        if (at == TY_STR) {
            diag(e->args[0]->span, E0202, SEV_ERROR, "opt<str> is not v0: opt carries a scalar or struct",
                 "hold strings on a struct or return result<i32, str> for failures");
            e->ty = TY_UNSET;
            return TY_UNSET;
        }
        const char *pcan = at == TY_STRUCT ? e->args[0]->tname : ty_name(at);
        char buf[192];
        snprintf(buf, sizeof buf, "opt_%s", pcan ? pcan : "?");
        const char *name = arena_dupstr(c->a, buf, strlen(buf));
        Payload pl;
        pl.ty = at;
        pl.tname = e->args[0]->tname;
        pl.span = e->args[0]->span;
        anon_declare(name, &pl, 1, sp);
        e->kind = EX_VARIANT;
        e->vname = "some";
        e->sval = name;
        e->bare_ctor = true;
        e->ty = TY_OPT;
        e->tname = name;
        return TY_OPT;
    }

    /* ctx known: aim the ctor at that opt/result, reuse variant checks */
    EnDecl *en = find_enum(c, wtn);
    int vi = -1;
    if (en) {
        if (strcmp(en->variants[0].name, vname) == 0) vi = 0;
        else if (strcmp(en->variants[1].name, vname) == 0) vi = 1;
    }
    if (!en || vi < 0) {
        char msg[240];
        const char *a = en ? en->variants[0].name : "some";
        const char *b = en ? en->variants[1].name : "none";
        snprintf(msg, sizeof msg, "'%s' does not construct %s (try %s or %s)",
                 vname, ty_disp(wty, wtn), a, b);
        diag(sp, E0202, SEV_ERROR, msg, "some/none build opt values, ok/err build result values");
        e->ty = TY_UNSET;
        return TY_UNSET;
    }
    Variant *v = &en->variants[vi];
    if (e->nargs != v->npayloads) {
        char msg[220];
        snprintf(msg, sizeof msg, "variant '%s' takes %d payload value(s), got %d",
                 v->name, v->npayloads, e->nargs);
        diag(sp, E0202, SEV_ERROR, msg, "match the payload count exactly");
        for (int k = 0; k < e->nargs; k++) tc_expr(c, e->args[k]);
        e->ty = TY_UNSET;
        return TY_UNSET;
    }
    for (int k = 0; k < e->nargs; k++) {
        Ty at = tc_expr_w(c, e->args[k], v->payloads[k].ty, v->payloads[k].tname);
        if (at == TY_UNSET) continue;
        if (!ty_same(at, e->args[k]->tname, v->payloads[k].ty, v->payloads[k].tname)) {
            char msg[260];
            snprintf(msg, sizeof msg,
                     "payload of '%s' is %s, got %s; no implicit conversion exists",
                     v->name, ty_disp(v->payloads[k].ty, v->payloads[k].tname),
                     ty_disp(at, e->args[k]->tname));
            diag(e->args[k]->span, E0202, SEV_ERROR, msg,
                 "types must match exactly; no implicit conversion exists");
        }
    }
    e->kind = EX_VARIANT;
    e->vname = vname;
    e->sval = en->name;
    e->bare_ctor = true;
    e->ty = wty;
    e->tname = en->name;
    return wty;
}

static Ty tc_expr(Ctx *c, Expr *e) {
    switch (e->kind) {
    case EX_INT: {
        /* literal type: fits i32 -> i32, fits i64 -> i64 */
        e->ty = (e->ival >= INT32_MIN && e->ival <= INT32_MAX) ? TY_I32 : TY_I64;
        return e->ty;
    }
    case EX_FLOAT: e->ty = TY_F64; return TY_F64;
    case EX_STR:  e->ty = TY_STR;  return TY_STR;
    case EX_BOOL: e->ty = TY_BOOL; return TY_BOOL;

    case EX_IDENT: {
        for (Scope *f = c->scopes; f; f = f->parent)
            for (int i = 0; i < f->nlocals; i++)
                if (strcmp(f->locals[i].name, e->sval) == 0) {
                    e->ty = f->locals[i].ty;
                    e->tname = f->locals[i].tname;
                    e->lvalue = true;
                    e->is_const_ref = f->locals[i].is_const;
                    return e->ty;
                }
        /* bare `none`: the no-payload opt constructor (payload ctors need()) */
        if (strcmp(e->sval, "none") == 0 && !find_fn(c, "none"))
            return tc_ctor(c, e, "none");
        /* a bare function name is a function-pointer value */
        {
            FnDecl *fn = find_fn(c, e->sval);
            if (fn) {
                /* build canonical signature */
                char buf[256]; size_t bi = 0;
                bi += (size_t)snprintf(buf + bi, sizeof buf - bi, "fn(");
                for (int i = 0; i < fn->nparams; i++) {
                    if (i) bi += (size_t)snprintf(buf + bi, sizeof buf - bi, ",");
                    const char *nm = fn->params[i].tname;
                    bi += (size_t)snprintf(buf + bi, sizeof buf - bi, "%s",
                        nm ? nm : ty_name(fn->params[i].ty));
                }
                bi += (size_t)snprintf(buf + bi, sizeof buf - bi, ")");
                if (fn->ret != TY_VOID) {
                    const char *rn = fn->retname;
                    bi += (size_t)snprintf(buf + bi, sizeof buf - bi, "->%s",
                        rn ? rn : ty_name(fn->ret));
                }
                const char *cname = arena_dupstr(c->a, buf, strlen(buf));
                (void)fn_type_declare(cname, fn->ret, fn->retname, NULL, 0, e->span);
                /* fix params in fn type: re-declare with params */
                FnTypeInfo *fi = fn_type_find(cname);
                if (fi) {
                    fi->nparams = fn->nparams;
                    for (int i = 0; i < fn->nparams && i < 8; i++) fi->params[i] = fn->params[i].ty;
                    fi->ret = fn->ret;
                    fi->ret_tname = fn->retname;
                }
                e->ty = TY_FN;
                e->tname = cname;
                return TY_FN;
            }
        }
        /* reported once at parse; no value, no cascade */
        if (strcmp(e->sval, "null") == 0) { e->ty = TY_UNSET; return TY_UNSET; }
        char msg[200];
        snprintf(msg, sizeof msg, "unknown identifier '%s' in this scope", e->sval);
        diag(e->span, E0201, SEV_ERROR, msg, "define it, use the right module, or fix spelling");
        e->ty = TY_UNSET;
        return TY_UNSET;
    }

    case EX_CALL: {
        /* bare opt/result ctors win only when no user fn takes the name */
        const char *nm = e->callee;
        bool ctor = strcmp(nm, "some") == 0 || strcmp(nm, "none") == 0 ||
                    strcmp(nm, "ok") == 0 || strcmp(nm, "err") == 0;
        if (ctor && !find_fn(c, nm)) return tc_ctor(c, e, nm);
        /* len: str uses strlen at runtime; fixed arrays are a compile-time N */
        if (strcmp(e->callee, "len") == 0 && e->nargs == 1) {
            Ty at = tc_expr(c, e->args[0]);
            if (at == TY_ARRAY) {
                ArrayInfo *ai = array_find(e->args[0]->tname);
                e->ty = TY_I32;
                e->ival = ai ? ai->len : 0;
                return e->ty;
            }
            if (at == TY_STR || at == TY_PTR8) { e->ty = TY_I32; return e->ty; }
            if (at != TY_UNSET) {
                char msg[220];
                snprintf(msg, sizeof msg, "len() takes an array or str, got %s",
                         ty_disp(at, e->args[0]->tname));
                diag(e->args[0]->span, E0202, SEV_ERROR, msg,
                     "len is defined for fixed arrays and str only");
            }
            e->ty = TY_I32;
            return e->ty;
        }
        int bret, bargc; Ty barg[4];
        memset(barg, 0, sizeof barg);
        if (builtin_info(e->callee, &bret, &bargc, barg)) {
            if (e->nargs != bargc) {
                char msg[200];
                snprintf(msg, sizeof msg, "builtin '%s' takes %d argument(s), got %d",
                         e->callee, bargc, e->nargs);
                diag(e->span, E0202, SEV_ERROR, msg, "match the signature exactly");
            } else {
                for (int i = 0; i < bargc; i++) {
                    Ty at = tc_expr_w(c, e->args[i], barg[i], NULL);
                    if (at == TY_UNSET || barg[i] == TY_UNSET) continue;
                    if (barg[i] == TY_FN && at == TY_FN) continue; /* any fn arity accepted */
                    if (!ty_same(at, e->args[i]->tname, barg[i], NULL) &&
                        !ty_fence_ok(at, barg[i])) {
                        char msg[240];
                        snprintf(msg, sizeof msg, "argument %d of '%s' must be %s, got %s",
                                 i + 1, e->callee,
                                 ty_name(barg[i]), ty_disp(at, e->args[i]->tname));
                        diag(e->args[i]->span, E0202, SEV_ERROR, msg,
                             "no implicit conversion exists in Tripon");
                    }
                }
            }
            e->ty = (Ty)bret;
            return e->ty;
        }
        FnDecl *fn = find_fn(c, e->callee);
        if (!fn) {
            char msg[200];
            snprintf(msg, sizeof msg, "call to unknown function '%s'", e->callee);
            diag(e->span, E0201, SEV_ERROR, msg, "declare it at top level or in an extern block");
            e->ty = TY_UNSET;
            return TY_UNSET;
        }
        if (e->nargs != fn->nparams) {
            char msg[220];
            snprintf(msg, sizeof msg, "'%s' takes %d argument(s), got %d",
                     fn->name, fn->nparams, e->nargs);
            diag(e->span, E0202, SEV_ERROR, msg, "count the parameters in the signature");
            for (int i = 0; i < e->nargs; i++) tc_expr(c, e->args[i]);
            e->ty = fn->ret;
            return e->ty;
        }
        for (int i = 0; i < e->nargs; i++) {
            Ty at = tc_expr_w(c, e->args[i], fn->params[i].ty, fn->params[i].tname);
            /* no cascades: if the argument already errored deeper, stop here */
            if (at == TY_UNSET || fn->params[i].ty == TY_UNSET) continue;
            if (!ty_same(at, e->args[i]->tname, fn->params[i].ty, fn->params[i].tname) &&
                !ty_fence_ok(at, fn->params[i].ty)) {
                char msg[260];
                snprintf(msg, sizeof msg, "argument %d of '%s' must be %s, got %s",
                         i + 1, fn->name,
                         ty_disp(fn->params[i].ty, fn->params[i].tname),
                         ty_disp(at, e->args[i]->tname));
                diag(e->args[i]->span, E0202, SEV_ERROR, msg,
                     "no implicit conversion exists in Tripon; cast<T> or declare the exact type");
            }
        }
        e->ty = fn->ret;
        e->tname = fn->retname;
        return e->ty;
    }

    case EX_UN:
        if (e->unop == UN_NOT) {
            Ty t = tc_expr(c, e->operand);
            if (t != TY_BOOL) {
                diag(e->operand->span, E0202, SEV_ERROR, "'!' requires bool",
                     "comparisons produce bool; there is no truthiness in Tripon");
            }
            e->ty = TY_BOOL;
            return TY_BOOL;
        }
        if (e->unop == UN_NEG) {
            Ty t = tc_expr(c, e->operand);
            if (!ty_is_num(t)) {
                diag(e->operand->span, E0202, SEV_ERROR, "'-' requires a number",
                     "arith ops exist only on numeric types");
                e->ty = TY_UNSET;
                return TY_UNSET;
            }
            /* negating unsigned is rejected outright */
            if (ty_is_int(t) && t >= TY_U8 && t <= TY_USIZE) {
                diag(e->operand->span, E0202, SEV_ERROR, "cannot negate an unsigned value",
                     "wrapping-neg of unsigned is not a thing; use a signed type");
                e->ty = TY_UNSET;
                return TY_UNSET;
            }
            e->ty = t;
            return t;
        }
        e->ty = TY_UNSET;
        return TY_UNSET;

    case EX_BIN: {
        Ty lhs = tc_expr(c, e->lhs);
        Ty rhs = tc_expr(c, e->rhs);
        int is_cmp = e->op == TK_LT || e->op == TK_GT || e->op == TK_LE || e->op == TK_GE;
        int is_eq = e->op == TK_EQ || e->op == TK_NE;
        int is_log = e->op == TK_AND || e->op == TK_OR;
        int is_arith = e->op == TK_PLUS || e->op == TK_MINUS ||
                       e->op == TK_STAR || e->op == TK_SLASH || e->op == TK_PERCENT ||
                       e->op == TK_POW;

        if (is_log) {
            if (lhs != TY_BOOL || rhs != TY_BOOL) {
                diag(e->span, E0202, SEV_ERROR, "logical ops require bool operands on both sides",
                     "there is no truthiness in Tripon; compare explicitly");
                e->ty = TY_UNSET;
                return TY_UNSET;
            }
            e->ty = TY_BOOL;
            return TY_BOOL;
        }

        if (lhs == TY_UNSET || rhs == TY_UNSET) {
            e->ty = TY_UNSET;
            return TY_UNSET;/* error already reported deeper */
        }

        /* literal adoption: int literal partner-side adoption when it fits */
        if (is_arith || is_cmp || is_eq) {
            if (e->lhs->kind == EX_INT && ty_is_num(rhs) && rhs != TY_BOOL) {
                Ty t = lit_adopt(e->lhs, rhs);
                if (t != TY_UNSET) { lhs = t; e->lhs->ty = t; }
            }
            if (e->rhs->kind == EX_INT && ty_is_num(lhs) && lhs != TY_BOOL) {
                Ty t = lit_adopt(e->rhs, lhs);
                if (t != TY_UNSET) { rhs = t; e->rhs->ty = t; }
            }
        }

        if (is_cmp || is_eq) {
            if (!ty_same(lhs, e->lhs->tname, rhs, e->rhs->tname) &&
                !ty_fence_ok(lhs, rhs)) {
                char msg[240];
                snprintf(msg, sizeof msg, "cannot compare %s with %s; no implicit conversion exists",
                         ty_disp(lhs, e->lhs->tname), ty_disp(rhs, e->rhs->tname));
                diag(e->span, E0202, SEV_ERROR, msg,
                     "same-type comparisons only; cast one side explicitly if that is the intent");
                e->ty = TY_UNSET;
                return TY_UNSET;
            }
            if (is_eq && !ty_is_num(lhs) && lhs != TY_BOOL) {
                if (lhs == TY_STR || lhs == TY_PTR8) {
                    /* str equality: byte-compare semantics, defined */
                    e->ty = TY_BOOL;
                    return TY_BOOL;
                }
                if (lhs == TY_ARRAY) {
                    diag(e->span, E0207, SEV_ERROR,
                         "array equality is not defined; compare element-by-element",
                         "write a loop and compare each index, or compare a hash");
                    e->ty = TY_BOOL;
                    return TY_BOOL;
                }
                /* composites have no generated equality in v0: E0207, not E0202 */
                char msg[240];
                snprintf(msg, sizeof msg, "composite equality on %s is not defined; no cast exists for it",
                         ty_disp(lhs, e->lhs->tname));
                diag(e->span, E0207, SEV_ERROR, msg,
                     "compare field by field, or match on an enum tag instead");
                e->ty = TY_UNSET;
                return TY_UNSET;
            }
            if (is_cmp && !ty_is_num(lhs)) {
                diag(e->span, E0202, SEV_ERROR, "'< > <= >=' need numeric operands",
                     "no cross-type comparisons exist in Tripon");
                e->ty = TY_UNSET;
                return TY_UNSET;
            }
            e->ty = TY_BOOL;
            return TY_BOOL;
        }

        if (is_arith) {
            if (!ty_is_num(lhs) || !ty_is_num(rhs) || !ty_same(lhs, e->lhs->tname, rhs, e->rhs->tname)) {
                char msg[260];
                snprintf(msg, sizeof msg, "%s and %s do not share an operator; no implicit conversion exists",
                         ty_disp(lhs, e->lhs->tname), ty_disp(rhs, e->rhs->tname));
                diag(e->span, E0202, SEV_ERROR, msg,
                     "types must match exactly; no implicit conversion exists; use cast<T>(x)");
                e->ty = TY_UNSET;
                return TY_UNSET;
            }
            if (e->op == TK_PERCENT && !ty_is_int(lhs)) {
                diag(e->span, E0202, SEV_ERROR, "'%' needs integer operands",
                     "float remainder is not a thing here; use fmod via extern if needed");
                e->ty = TY_UNSET;
                return TY_UNSET;
            }
            if (e->op == TK_POW && !ty_is_float(lhs)) {
                diag(e->span, E0202, SEV_ERROR, "'**' needs float operands in v0",
                     "integer pow lands with the stdlib math module");
                e->ty = TY_UNSET;
                return TY_UNSET;
            }
            e->ty = lhs;
            e->tname = e->lhs->tname;
            return lhs;
        }
        e->ty = TY_UNSET;
        return TY_UNSET;
    }

    case EX_INDEX: {
        Ty bt = tc_expr(c, e->base);
        if (bt == TY_UNSET) { e->ty = TY_UNSET; return TY_UNSET; }
        if (bt == TY_ARRAY) {
            ArrayInfo *ai = array_find(e->base->tname);
            if (!ai) {
                diag(e->base->span, E0202, SEV_ERROR, "unknown array type",
                     "the array type was not registered by the parser");
                e->ty = TY_UNSET;
                return TY_UNSET;
            }
            Ty it = tc_expr(c, e->index);
            if (it != TY_UNSET && !ty_is_int(it)) {
                char msg[220];
                snprintf(msg, sizeof msg, "array index must be an integer, got %s",
                         ty_disp(it, e->index->tname));
                diag(e->index->span, E0202, SEV_ERROR, msg,
                     "indexes are i8..u64; cast the value explicitly if needed");
            } else if (it != TY_UNSET) {
                long long k;
                if (idx_lit(e->index, &k) && (k < 0 || k >= ai->len)) {
                    char msg[220], hint[160];
                    snprintf(msg, sizeof msg, "index %lld is out of bounds for [%d]",
                             k, ai->len);
                    snprintf(hint, sizeof hint, "valid indexes are 0 through %d",
                             ai->len - 1);
                    diag(e->index->span, E0202, SEV_ERROR, msg, hint);
                }
            }
            e->ty = ai->elem_ty;
            e->tname = ai->elem_tname;
            e->lvalue = e->base->lvalue;
            e->is_const_ref = e->base->is_const_ref;
            return e->ty;
        }
        if (bt == TY_STR || bt == TY_PTR8) {
            Ty it = tc_expr(c, e->index);
            if (it != TY_UNSET && !ty_is_int(it)) {
                char msg[220];
                snprintf(msg, sizeof msg, "str index must be an integer, got %s",
                         ty_disp(it, e->index->tname));
                diag(e->index->span, E0202, SEV_ERROR, msg,
                     "indexes are i8..u64; cast the value explicitly if needed");
            }
            e->ty = TY_U8;              /* one byte */
            e->tname = NULL;
            e->lvalue = false;
            e->is_const_ref = false;
            return TY_U8;
        }
        char msg[220];
        snprintf(msg, sizeof msg, "indexing needs an array or str, got %s",
                 ty_disp(bt, e->base->tname));
        diag(e->base->span, E0202, SEV_ERROR, msg,
             "only fixed arrays and str support [i] in v0");
        tc_expr(c, e->index);
        e->ty = TY_UNSET;
        return TY_UNSET;
    }

    case EX_FIELD: {
        Ty bt = tc_expr(c, e->base);
        if (bt == TY_UNSET) { e->ty = TY_UNSET; return TY_UNSET; }
        if (bt != TY_STRUCT) {
            char msg[200];
            snprintf(msg, sizeof msg, "field access needs a struct value, not %s",
                     ty_disp(bt, e->base->tname));
            diag(e->base->span, E0202, SEV_ERROR, msg,
                 "structs carry named fields; enums are matched, not read field-wise");
            e->ty = TY_UNSET;
            return TY_UNSET;
        }
        StDecl *st = find_struct(c, e->base->tname);
        if (!st) { e->ty = TY_UNSET; return TY_UNSET; }
        for (int i = 0; i < st->nfields; i++)
            if (strcmp(st->fields[i].name, e->sval) == 0) {
                e->ty = st->fields[i].ty;
                e->tname = st->fields[i].tname;
                /* value semantics: field lvalue derives from the base binding */
                e->lvalue = e->base->lvalue;
                e->is_const_ref = e->base->is_const_ref;
                return e->ty;
            }
        char msg[200];
        snprintf(msg, sizeof msg, "struct '%s' has no field '%s'", st->name, e->sval);
        diag(e->span, E0202, SEV_ERROR, msg, "check the field list in the struct decl");
        e->ty = TY_UNSET;
        return TY_UNSET;
    }

    case EX_STRUCTINIT: {
        StDecl *st = find_struct(c, e->sval);
        if (!st) {
            char msg[200];
            snprintf(msg, sizeof msg, "unknown struct type '%s'", e->sval);
            diag(e->span, E0201, SEV_ERROR, msg, "declare it before constructing values");
            e->ty = TY_UNSET;
            return TY_UNSET;
        }
        e->ty = TY_STRUCT;
        e->tname = st->name;
        /* every field exactly once; extra field names rejected in order */
        for (int i = 0; i < e->nargs; i++) {
            int idx = -1;
            for (int j = 0; j < st->nfields; j++)
                if (strcmp(st->fields[j].name, e->inames[i]) == 0) { idx = j; break; }
            if (idx < 0) {
                char msg[200];
                snprintf(msg, sizeof msg, "struct '%s' has no field '%s'", st->name, e->inames[i]);
                diag(e->span, E0202, SEV_ERROR, msg, "check the field list in the struct decl");
                tc_expr(c, e->args[i]);
                continue;
            }
            if (st->fields[idx].ty == TY_ARRAY) {
                diag(e->args[i]->span, E0202, SEV_ERROR,
                     "array fields cannot be set in a struct literal in v0",
                     "declare the struct with let, then assign array elements");
                tc_expr(c, e->args[i]);
                continue;
            }
            Ty it = tc_expr_w(c, e->args[i], st->fields[idx].ty, st->fields[idx].tname);
            if (it == TY_UNSET) continue;
            Ty fty = st->fields[idx].ty;
            const char *fnm = st->fields[idx].tname;
            if (!ty_same(it, e->args[i]->tname, fty, fnm)) {
                char msg[260];
                snprintf(msg, sizeof msg, "field '%s' is %s, init is %s; no implicit conversion exists",
                         e->inames[i], ty_disp(fty, fnm), ty_disp(it, e->args[i]->tname));
                diag(e->args[i]->span, E0202, SEV_ERROR, msg,
                     "types must match exactly; no implicit conversion exists");
            }
        }
        for (int j = 0; j < st->nfields; j++) {
            bool seen = false;
            for (int i = 0; i < e->nargs; i++)
                if (strcmp(e->inames[i], st->fields[j].name) == 0 && !seen) seen = true;
                else if (strcmp(e->inames[i], st->fields[j].name) == 0 && seen) {
                    char msg[200];
                    snprintf(msg, sizeof msg, "field '%s' is initialized twice", st->fields[j].name);
                    diag(e->span, E0202, SEV_ERROR, msg, "one init per declared field");
                }
            if (!seen) {
                char msg[200];
                snprintf(msg, sizeof msg, "missing field '%s' in struct init", st->fields[j].name);
                diag(e->span, E0202, SEV_ERROR, msg, "initialize every declared field");
                break;  /* first gap only: fix spans stay one error at a time */
            }
        }
        return e->ty;
    }

    case EX_VARIANT: {
        EnDecl *en = find_enum(c, e->sval);
        if (!en) {
            char msg[200];
            snprintf(msg, sizeof msg, "unknown enum type '%s'", e->sval);
            diag(e->span, E0201, SEV_ERROR, msg, "declare it before constructing values");
            e->ty = TY_UNSET;
            return TY_UNSET;
        }
        e->ty = TY_ENUM;
        e->tname = en->name;
        for (int i = 0; i < en->nvariants; i++) {
            if (strcmp(en->variants[i].name, e->vname) != 0) continue;
            Variant *v = &en->variants[i];
            if (e->nargs != v->npayloads) {
                char msg[220];
                snprintf(msg, sizeof msg, "variant '%s' takes %d payload value(s), got %d",
                         v->name, v->npayloads, e->nargs);
                diag(e->span, E0202, SEV_ERROR, msg, "match the variant payload types exactly");
            }
            for (int k = 0; k < e->nargs && k < v->npayloads; k++) {
                Ty at = tc_expr_w(c, e->args[k], v->payloads[k].ty, v->payloads[k].tname);
                if (at == TY_UNSET) continue;
                if (!ty_same(at, e->args[k]->tname, v->payloads[k].ty, v->payloads[k].tname)) {
                    char msg[260];
                    snprintf(msg, sizeof msg, "payload %d of '%s::%s' is %s, got %s",
                             k + 1, en->name, v->name,
                             ty_disp(v->payloads[k].ty, v->payloads[k].tname),
                             ty_disp(at, e->args[k]->tname));
                    diag(e->args[k]->span, E0202, SEV_ERROR, msg,
                         "types must match exactly; no implicit conversion exists");
                }
            }
            return e->ty;
        }
        char msg[200];
        snprintf(msg, sizeof msg, "enum '%s' has no variant '%s'", en->name, e->vname);
        diag(e->span, E0201, SEV_ERROR, msg, "check the variant list in the enum decl");
        e->ty = TY_UNSET;
        return TY_UNSET;
    }

    case EX_SPREAD: {
        if (!c->spread_pos) {
            diag(e->operand->span, E0101, SEV_ERROR,
                 "the '?' spread is statement-level in v0 (let x = e?; e?; return e?;)",
                 "hoist the wrapped expr into a let, then spread it");
            tc_expr(c, e->operand);
            e->ty = TY_UNSET;
            return TY_UNSET;
        }
        Ty bt = tc_expr(c, e->operand);
        if (bt == TY_UNSET) { e->ty = TY_UNSET; return TY_UNSET; }
        if (bt != TY_OPT && bt != TY_RESULT) {
            char msg[220];
            snprintf(msg, sizeof msg, "'?' spreads opt/result values, got %s",
                     ty_disp(bt, e->operand->tname));
            diag(e->operand->span, E0202, SEV_ERROR, msg,
                 "unwrap with match or make the source opt/result");
            e->ty = TY_UNSET;
            return TY_UNSET;
        }
        /* propagating out: the fn must return the very same shape */
        FnDecl *fn = c->cur_fn;
        Ty rty = fn ? fn->ret : TY_UNSET;
        if (rty != bt || !ty_same(rty, fn->retname, bt, e->operand->tname)) {
            /* report, but keep the payload type flowing to kill cascades */
            EnDecl *en2 = anon_find(e->operand->tname);
            if (en2 && en2->variants[0].npayloads == 1) {
                e->ty = en2->variants[0].payloads[0].ty;
                e->tname = en2->variants[0].payloads[0].tname;
            }
            if (rty == TY_OPT || rty == TY_RESULT) {
                char msg[260];
                snprintf(msg, sizeof msg, "cannot spread %s out of a fn returning %s",
                         ty_disp(bt, e->operand->tname), ty_disp(rty, fn->retname));
                diag(e->operand->span, E0202, SEV_ERROR, msg,
                     "the failure payload must be the caller's own E/none");
            } else {
                char msg[280];
                snprintf(msg, sizeof msg,
                         "'?' inside a fn returning %s cannot propagate; match it or return %s",
                         ty_disp(rty, fn->retname), ty_disp(bt, e->operand->tname));
                diag(e->operand->span, E0205, SEV_ERROR, msg,
                     "make this fn return the same opt/result shape to use ? here");
            }
            return e->ty;
        }
        EnDecl *en = anon_find(e->operand->tname);
        if (!en || en->variants[0].npayloads != 1) { e->ty = TY_UNSET; return TY_UNSET; }
        e->ty = en->variants[0].payloads[0].ty;
        e->tname = en->variants[0].payloads[0].tname;
        e->lvalue = e->operand->lvalue;
        return e->ty;
    }

    case EX_CAST: {
        Ty st = tc_expr(c, e->operand);
        if (st == TY_UNSET) return e->ty;   /* operand already reported; no cascade */
        /* the one conversion table (tripon.md T2): int<->int, float<->float,
         * float->int truncates toward zero, int->float is exact. bool/str/composites deny. */
        bool ok = (ty_is_int(e->ty) && ty_is_int(st)) ||
                  (ty_is_float(e->ty) && ty_is_float(st)) ||
                  (ty_is_int(e->ty) && ty_is_float(st)) ||
                  (ty_is_float(e->ty) && ty_is_int(st));
        if (!ok) {
            char msg[240];
            snprintf(msg, sizeof msg, "cast<%s> from %s is not a defined conversion",
                     ty_disp(e->ty, e->sval), ty_disp(st, e->operand->tname));
            diag(e->span, E0207, SEV_ERROR, msg,
                 "no implicit conversions exist; use cast<T>(x) for exact or explicit lossy casts");
        }
        return e->ty;
    }
    }
    e->ty = TY_UNSET;
    return TY_UNSET;
}

/* ---------------- statements ---------------- */

static void tc_stmt(Ctx *c, Stmt *s);
static void tc_match(Ctx *c, Stmt *s);

static void tc_block(Ctx *c, Stmt **body, int nbody) {
    Scope keep;
    memset(&keep, 0, sizeof keep);
    keep.parent = c->scopes;
    c->scopes = (Scope *)arena_zalloc(c->a, sizeof(Scope));
    c->scopes->parent = keep.parent;
    for (int i = 0; i < nbody; i++) tc_stmt(c, body[i]);
    c->scopes = c->scopes->parent ? c->scopes->parent : NULL;
    c->scopes = keep.parent;
}

static void tc_stmt(Ctx *c, Stmt *s) {
    switch (s->kind) {
    case ST_LET: {
        Ty declared = s->ty;
        if (s->ty == TY_TYPEDEF) s->ty = resolve_tname(c, s->tname, s->span);
        declared = s->ty;
        if (declared == TY_UNSET) {
            if (s->init) {
                int was = c->spread_pos;
                c->spread_pos = 1;
                declared = tc_expr(c, s->init);
                c->spread_pos = was;
            } else {
                diag(s->span, E0101, SEV_ERROR, "binding with no type and no initializer cannot be inferred",
                     "write 'let x: T;' for zero-init or 'let x = expr;'");
                declared = TY_UNSET;
            }
        } else if (s->init) {
            int was = c->spread_pos;
            c->spread_pos = 1;
            Ty it = tc_expr_w(c, s->init, declared, s->tname);
            c->spread_pos = was;
            if (!ty_same(it, s->init->tname, declared, s->tname) &&
                !ty_fence_ok(it, declared)) {
                char msg[240];
                snprintf(msg, sizeof msg, "initializer is %s but binding is %s; no implicit conversion exists",
                         it == TY_UNSET ? "unknown" : ty_disp(it, s->init->tname),
                         ty_disp(declared, s->tname));
                diag(s->init->span, E0202, SEV_ERROR, msg,
                     "types must match exactly; no implicit conversion exists; use cast<T>(x)");
            }
        } else {
            /* typed, no init: zero-init is the defined default */
        }
        if (declared == TY_VOID) {
            diag(s->span, E0202, SEV_ERROR, "cannot bind a value of type ()",
                 "() is a unit type, not data");
            declared = TY_UNSET;
        }
        /* write back so codegen emits the inferred type */
        s->ty = declared;
        if (declared != TY_STRUCT && declared != TY_ENUM &&
            declared != TY_OPT && declared != TY_RESULT &&
            declared != TY_ARRAY) s->tname = NULL;
        else if (s->init && !s->tname) s->tname = s->init->tname;
        scope_insert(c, s->name, declared, s->tname, s->is_const, s->span);
        break;
    }
    case ST_ASSIGN: {
        Ty tt = tc_expr(c, s->target);
        if (s->target->kind == EX_INDEX && s->target->base &&
            s->target->base->ty == TY_STR) {
            diag(s->target->span, E0202, SEV_ERROR,
                 "str is immutable in v0; cannot assign to s[i]",
                 "copy bytes into a [N]u8 array instead");
            tc_expr(c, s->value);
            break;
        }
        int was = c->spread_pos;
        c->spread_pos = 1;
        Ty vt = tc_expr_w(c, s->value, tt, s->target->tname);
        c->spread_pos = was;
        if (tt == TY_UNSET || vt == TY_UNSET) break;
        if (!s->target->lvalue) {
            diag(s->target->span, E0202, SEV_ERROR, "assignment target must be a binding",
                 "assign to a let/const-declared binding");
        }
        if (s->target->is_const_ref) {
            const char *nm = s->target->kind == EX_IDENT ? s->target->sval : s->target->base->sval;
            char msg[220];
            snprintf(msg, sizeof msg, "%s is const and cannot be reassigned", nm);
            diag(s->span, E0203, SEV_ERROR, msg, "declared const but reassigned; switch to let");
            break;
        }
        bool is_op = s->aop != TK_ASSIGN;
        /* literal adoption as above */
        if (s->value->kind == EX_INT && ty_is_num(tt) && tt != TY_BOOL) {
            Ty t = lit_adopt(s->value, tt);
            if (t != TY_UNSET) { vt = t; s->value->ty = t; }
        }
        if (is_op && !ty_is_num(tt)) {
            char msg[260];
            snprintf(msg, sizeof msg, "cannot apply op to %s target; no implicit conversion exists",
                     ty_disp(tt, s->target->tname));
            diag(s->value->span, E0202, SEV_ERROR, msg,
                 "compound assignment exists on numeric types only");
            break;
        }
        if (!ty_same(tt, s->target->tname, vt, s->value->tname)) {
            char msg[260];
            snprintf(msg, sizeof msg, "cannot %s %s to %s; no implicit conversion exists",
                     is_op ? "apply op and assign" : "assign",
                     ty_disp(vt, s->value->tname), ty_disp(tt, s->target->tname));
            diag(s->value->span, E0202, SEV_ERROR, msg,
                 "types must match exactly; no implicit conversion exists; use cast<T>(x)");
        }
        break;
    }
    case ST_RETURN: {
        Ty fnret = c->cur_fn ? c->cur_fn->ret : TY_UNSET;
        const char *frn = c->cur_fn ? c->cur_fn->retname : NULL;
        Ty t;
        if (s->value) {
            int was = c->spread_pos;
            c->spread_pos = 1;
            t = tc_expr_w(c, s->value, fnret, frn);
            c->spread_pos = was;
        } else {
            t = TY_VOID;
        }
        if (s->value == NULL && fnret != TY_VOID && fnret != TY_UNSET) {
            diag(s->span, E0202, SEV_ERROR, "return needs a value; the fn returns one",
                 "bare return belongs in () fns");
            break;
        }
        if (s->value != NULL && fnret == TY_VOID) {
            diag(s->span, E0202, SEV_ERROR, "fn returns () but return carries a value",
                 "drop the value or change the fn return type");
            break;
        }
        if (s->value != NULL && fnret != TY_UNSET && fnret != TY_VOID &&
            s->value->kind != EX_SPREAD &&   /* spread errors carry their own diag */
            !ty_same(t, s->value->tname, fnret, frn)) {
            char msg[240];
            snprintf(msg, sizeof msg, "return is %s but fn returns %s; no implicit conversion exists",
                     t == TY_UNSET ? "unknown" : ty_disp(t, s->value->tname),
                     ty_disp(fnret, frn));
            diag(s->value->span, E0202, SEV_ERROR, msg,
                 "types must match exactly; no implicit conversion exists; use cast<T>(x)");
        }
        break;
    }
    case ST_IF:
    case ST_WHILE: {
        Ty t = tc_expr(c, s->cond);
        if (t != TY_BOOL) {
            diag(s->cond->span, E0202, SEV_ERROR, "condition must be bool",
                 "no truthiness exists in Tripon; compare explicitly (x == 0)");
        }
        tc_block(c, s->body, s->nbody);
        if (s->els) {
            if (s->els->kind == ST_IF) tc_stmt(c, s->els);
            else tc_block(c, s->els->body, s->els->nbody);
        }
        break;
    }
    case ST_EXPR: {
        int was = c->spread_pos;
        c->spread_pos = 1;
        Ty t = tc_expr(c, s->value);
        c->spread_pos = was;
        /* T4: an opt/result evaluated and dropped is the E0205 trigger */
        if (t == TY_OPT || t == TY_RESULT) {
            char msg[240];
            snprintf(msg, sizeof msg, "%s value evaluated and dropped",
                     ty_disp(t, s->value->tname));
            diag(s->value->span, E0205, SEV_ERROR, msg,
                 "bind it (let r = expr;) then spread with ? or match on it explicitly");
        }
        break;
    }
    case ST_BLOCK: {
        tc_block(c, s->body, s->nbody);
        break;
    }
    case ST_MATCH:
        tc_match(c, s);
        break;
    default: break;
    }
}

/* ---------------- match checking (T5 + T2) ---------------- */

/* arm body in its own scope; payload pattern vars land there with their types */
static void tc_arm_body(Ctx *c, MatchArm *arm, Variant *v) {
    Scope *inner = (Scope *)arena_zalloc(c->a, sizeof(Scope));
    inner->parent = c->scopes;
    c->scopes = inner;
    for (int k = 0; k < arm->nbinds && v && k < v->npayloads; k++) {
        scope_insert(c, arm->binds[k], v->payloads[k].ty, v->payloads[k].tname, false, arm->span);
    }
    for (int i = 0; i < arm->nbody; i++) tc_stmt(c, arm->body[i]);
    c->scopes = inner->parent;
}

static void tc_match(Ctx *c, Stmt *s) {
    Ty st = tc_expr(c, s->cond);
    const char *snm = s->cond->tname;
    bool enum_match = st == TY_ENUM || st == TY_OPT || st == TY_RESULT;
    bool num_match = ty_is_int(st) || st == TY_BOOL;
    if (!enum_match && !num_match) {
        char msg[240];
        snprintf(msg, sizeof msg, "match needs an enum or numeric value, got %s",
                 st == TY_UNSET ? "unknown" : ty_disp(st, snm));
        diag(s->span, E0202, SEV_ERROR, msg,
             "use an enum for variant matching, bool/int for flag matching");
    }
    EnDecl *en = enum_match ? find_enum(c, snm) : NULL;

    /* coverage marks: enum -> variant indexes; literals -> dup check only */
    bool *covered = arena_zalloc(c->a, sizeof(bool) * (size_t)(en ? en->nvariants : 1));
    bool saw_wild = false;
    long long lit_val[64];
    int nlit = 0;
    int lit_bool[2] = {0, 0};

    for (int a = 0; a < s->narms; a++) {
        MatchArm *arm = s->arms[a];
        if (arm->pkind == PAT_WILD) {
            if (saw_wild) {
                diag(arm->span, E0212, SEV_ERROR, "duplicate match arm: '_' covers everything after the first",
                     "keep one wildcard, usually last");
            }
            saw_wild = true;
            tc_arm_body(c, arm, NULL);
            continue;
        }
        if (saw_wild) {
            diag(arm->span, E0212, SEV_ERROR, "unreachable match arm: an earlier '_' covers everything",
                 "remove or reorder the arm; match arms are checked top to bottom");
            continue;
        }
        if (arm->pkind == PAT_LIT_INT) {
            if (!num_match || st == TY_BOOL) {
                diag(arm->span, E0202, SEV_ERROR, "integer pattern needs an integer match value",
                     "match arms must match the matched type exactly");
                continue;
            }
            for (int i = 0; i < nlit; i++)
                if (lit_val[i] == arm->ival) {
                    char msg[200];
                    snprintf(msg, sizeof msg, "duplicate match arm: %lld already covered",
                             (long long)arm->ival);
                    diag(arm->span, E0212, SEV_ERROR, msg,
                         "remove or reorder the repeated arm; match arms are checked top to bottom");
                }
            if (nlit < (int)(sizeof lit_val / sizeof lit_val[0])) lit_val[nlit++] = arm->ival;
            tc_arm_body(c, arm, NULL);
        } else if (arm->pkind == PAT_LIT_BOOL) {
            if (st != TY_BOOL) {
                diag(arm->span, E0202, SEV_ERROR, "bool pattern needs a bool match value",
                     "match arms must match the matched type exactly");
                continue;
            }
            if (lit_bool[arm->bval]) {
                char msg[200];
                snprintf(msg, sizeof msg, "duplicate match arm: %s already covered", arm->bval ? "true" : "false");
                diag(arm->span, E0212, SEV_ERROR, msg,
                     "remove the repeated arm; match arms are checked top to bottom");
            }
            lit_bool[arm->bval] = 1;
            tc_arm_body(c, arm, NULL);
        } else { /* PAT_VARIANT */
            if (!enum_match) {
                diag(arm->span, E0202, SEV_ERROR, "variant pattern needs an enum match value",
                     "use Enum::Variant patterns only on enum matches");
                continue;
            }
            EnDecl *aen = en;
            if (arm->ename) {
                aen = find_enum(c, arm->ename);
                if (!aen) {
                    char msg[200];
                    snprintf(msg, sizeof msg, "unknown enum '%s' in pattern", arm->ename);
                    diag(arm->span, E0201, SEV_ERROR, msg, "check spelling or declare the enum");
                    continue;
                }
                if (aen != en) {
                    char msg[240];
                    snprintf(msg, sizeof msg, "pattern '%s::%s' does not belong to enum '%s'",
                             arm->ename, arm->vname, en->name);
                    diag(arm->span, E0202, SEV_ERROR, msg, "patterns must match the matched enum");
                    continue;
                }
            } else {
                /* bare ident: resolve in the matched enum */
                bool ok = false;
                for (int v = 0; v < en->nvariants; v++)
                    if (strcmp(en->variants[v].name, arm->vname) == 0) { ok = true; break; }
                if (!ok) {
                    char msg[240];
                    snprintf(msg, sizeof msg, "bare variant '%s' is not a variant of '%s'",
                             arm->vname, en->name);
                    diag(arm->span, E0202, SEV_ERROR, msg, "use the qualified Enum::Variant form");
                    continue;
                }
            }
            Variant *v = NULL;
            int vi = 0;
            for (; vi < aen->nvariants; vi++)
                if (strcmp(aen->variants[vi].name, arm->vname) == 0) { v = &aen->variants[vi]; break; }
            if (!v) {
                char msg[200];
                snprintf(msg, sizeof msg, "enum '%s' has no variant '%s'", aen->name, arm->vname);
                diag(arm->span, E0201, SEV_ERROR, msg, "check the variant list in the enum decl");
                continue;
            }
            if (covered[vi]) {
                char msg[200];
                snprintf(msg, sizeof msg, "duplicate match arm: variant '%s' already covered", v->name);
                diag(arm->span, E0212, SEV_ERROR, msg,
                     "remove the repeated arm; match arms are checked top to bottom");
            }
            covered[vi] = true;
            /* payload arity must match exactly; binds then type with payload types */
            if (arm->nbinds != v->npayloads) {
                char msg[220];
                if (arm->nbinds == 0) {
                    snprintf(msg, sizeof msg,
                             "variant '%s' carries %d payload value(s); bind them in the pattern",
                             v->name, v->npayloads);
                } else {
                    snprintf(msg, sizeof msg, "variant '%s' has %d payload value(s), pattern binds %d",
                             v->name, v->npayloads, arm->nbinds);
                }
                diag(arm->span, E0202, SEV_ERROR, msg, "one binding per payload value");
                continue;
            }
            tc_arm_body(c, arm, v);
        }
    }

    /* T5: exhaustive over enums; a deliberate '_' arm makes gaps legal.
     * one gap gets the one fix span */
    if (en && !saw_wild)
        for (int vi = 0; vi < en->nvariants; vi++)
            if (!covered[vi]) {
                char msg[240];
                snprintf(msg, sizeof msg, "match over '%s' misses variant '%s'",
                         en->name, en->variants[vi].name);
                diag(s->span, E0206, SEV_ERROR, msg,
                     "cover every variant or add a deliberate '_' arm");
                break;
            }
}

void typecheck_file(Arena *a, Decl **decls, int ndecls) {
    Ctx c;
    memset(&c, 0, sizeof c);
    c.a = a;

    prepass_fns(&c, decls, ndecls);
    prepass_types(&c, decls, ndecls);   /* also resolves fn param/return types */

    /* global scope: top-level let/const bindings are visible in every fn */
    Scope *global_scope = arena_zalloc(c.a, sizeof(Scope));
    for (int i = 0; i < ndecls; i++) {
        if (decls[i]->kind != D_LET) continue;
        Decl *d = decls[i];
        if (d->ty == TY_TYPEDEF) d->ty = resolve_tname(&c, d->tname, d->span);
        if (d->ty == TY_UNSET) d->ty = TY_I32;
        if (d->init) {
            c.scopes = global_scope;
            Ty at = tc_expr_w(&c, d->init, d->ty, d->tname);
            if (at != TY_UNSET && !ty_same(at, d->init->tname, d->ty, d->tname))
                diag(d->init->span, E0202, SEV_ERROR, "global init type mismatch", "types must match");
        }
        Local *na = arena_alloc(c.a, sizeof(Local) * (size_t)(global_scope->nlocals + 1));
        if (global_scope->nlocals) memcpy(na, global_scope->locals, sizeof(Local) * (size_t)global_scope->nlocals);
        na[global_scope->nlocals] = (Local){d->name, d->ty, d->tname, d->is_const, d->span};
        global_scope->locals = na;
        global_scope->nlocals++;
    }

    bool have_main = false;
    for (int i = 0; i < c.nfuncs; i++)
        if (strcmp(c.funcs[i]->name, "main") == 0 && !c.funcs[i]->is_extern) {
            have_main = true;
            FnDecl *m = c.funcs[i];
            if (m->nparams != 0) {
                diag(m->span, E0501, SEV_ERROR, "fn main() takes no parameters",
                     "args access arrives with the runtime module");
            }
            if (m->ret != TY_I32 && m->ret != TY_VOID) {
                diag(m->span, E0501, SEV_ERROR, "fn main() must return i32 or ()",
                     "i32 becomes the process exit code");
            }
            c.cur_fn = m;
            c.scopes = global_scope;
            tc_block(&c, m->body, m->nbody);
            c.cur_fn = NULL;
        }
    if (!have_main) {
        Span sp = {0};
        sp.line = 1; sp.col = 1; sp.len = 1;
        diag(sp, E0501, SEV_ERROR, "no fn main() found in this file",
             "define fn main() -> i32 or mark an explicit entry target");
    }

    /* typecheck the rest of the non-main functions too */
    for (int i = 0; i < c.nfuncs; i++) {
        if (strcmp(c.funcs[i]->name, "main") == 0 || c.funcs[i]->is_extern) continue;
        FnDecl *fn = c.funcs[i];
        c.cur_fn = fn;
        c.scopes = global_scope;
        Scope *_fnsc = arena_zalloc(c.a, sizeof(Scope));
        _fnsc->parent = global_scope;
        c.scopes = _fnsc;
        for (int k = 0; k < fn->nparams; k++) {
            scope_insert(&c, fn->params[k].name, fn->params[k].ty, fn->params[k].tname,
                         false, fn->params[k].span);
        }
        for (int k = 0; k < fn->nbody; k++) tc_stmt(&c, fn->body[k]);
        c.cur_fn = NULL;
    }
}
