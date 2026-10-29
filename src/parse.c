/* parse.c - recursive descent per spec/grammar.ebnf (P1.0 subset).
 * Structs/enums/match parse now, error with "lands in P1.1" diagnostics. */
#include "common.h"

typedef struct {
    Token *toks;
    int ntoks, pos;
    Arena *a;
    const char *file;
    int si_ok;      /* struct-init IDENT '{' currently allowed (suppressed in if/while/match conditions) */
    int no_anon;    /* struct fields / enum payloads deny opt/result types in v0 */
} Parser;

static Token *peek(Parser *p) { return &p->toks[p->pos]; }
static Token *peekn(Parser *p, int n) { int i = p->pos + n; if (i >= p->ntoks) i = p->ntoks - 1; return &p->toks[i]; }

static Token *advance(Parser *p) {
    Token *t = &p->toks[p->pos];
    if (t->kind != TK_EOF) p->pos++;
    return t;
}

static bool at(Parser *p, TokKind k) { return peek(p)->kind == k; }

static bool eat(Parser *p, TokKind k) {
    if (at(p, k)) { advance(p); return true; }
    return false;
}

static Token *expect_token(Parser *p, TokKind k, const char *what) {
    if (at(p, k)) return advance(p);
    Span sp = peek(p)->span;
    char msg[220];
    snprintf(msg, sizeof msg, "expected %s, got %s", what, tok_kind_word(peek(p)->kind));
    diag(sp, E0101, SEV_ERROR, msg, "see spec/grammar.ebnf for the legal shapes here");
    return &p->toks[p->pos];
}

/* ---------------- types ---------------- */

/* Builtins map straight to Ty. Any other ident is a nominal struct/enum name
 * (TY_TYPEDEF): the typecheck pre-pass resolves it against the decl tables. */
static Ty parse_type(Parser *p, const char **tname) {
    if (tname) *tname = NULL;
    /* fixed array: "[" Num "]" Type (grammar.ebnf ArrayType). No slice in v0. */
    if (at(p, TK_LB)) {
        Token *lb = advance(p);
        Token *num = expect_token(p, TK_INT, "an array length");
        expect_token(p, TK_RB, "']' after the array length");
        const char *en = NULL;
        Ty et = parse_type(p, &en);
        if (num->ival <= 0 || num->ival > 2147483647LL)
            diag(num->span, E0202, SEV_ERROR, "array length must be in 1..2147483647",
                 "fixed arrays have at least one element");
        if (et == TY_VOID)
            diag(lb->span, E0202, SEV_ERROR, "arrays of () are not data",
                 "use a scalar, str, or struct element type");
        const char *edisp = (et == TY_TYPEDEF || et == TY_STRUCT || et == TY_ENUM ||
                             et == TY_OPT || et == TY_RESULT || et == TY_ARRAY)
                          ? en : ty_name(et);
        char buf[192];
        snprintf(buf, sizeof buf, "[%lld]%s", num->ival, edisp ? edisp : "?");
        const char *name = arena_dupstr(p->a, buf, strlen(buf));
        array_declare(name, (int)num->ival, et, en, lb->span);
        if (tname) *tname = name;
        return TY_ARRAY;
    }
    if (eat(p, TK_LP) && eat(p, TK_RP)) {
        return TY_VOID;     /* "()" = unit/void */
    }
    if (at(p, TK_FN)) {
        Token *fk = advance(p);
        expect_token(p, TK_LP, "'(' after fn");
        Ty params[8]; int nparams = 0;
        if (!at(p, TK_RP)) {
            while (1) {
                const char *pn = NULL;
                Ty pt = parse_type(p, &pn);
                if (nparams < 8) params[nparams++] = pt;
                if (!eat(p, TK_COMMA)) break;
            }
        }
        expect_token(p, TK_RP, "')' to close fn params");
        Ty ret = TY_VOID;
        const char *rtn = NULL;
        if (eat(p, TK_ARROW)) { ret = parse_type(p, &rtn); }
        /* canonical name */
        char buf[256]; size_t bi = 0;
        bi += (size_t)snprintf(buf + bi, sizeof buf - bi, "fn(");
        for (int i = 0; i < nparams; i++) {
            if (i) bi += (size_t)snprintf(buf + bi, sizeof buf - bi, ",");
            const char *nm = (i < nparams) ? NULL : NULL;
            (void)nm;
            bi += (size_t)snprintf(buf + bi, sizeof buf - bi, "%s", ty_name(params[i]));
        }
        bi += (size_t)snprintf(buf + bi, sizeof buf - bi, ")");
        if (ret != TY_VOID) {
            bi += (size_t)snprintf(buf + bi, sizeof buf - bi, "->%s", ty_name(ret));
        }
        const char *cname = arena_dupstr(p->a, buf, strlen(buf));
        fn_type_declare(cname, ret, rtn, params, nparams, fk->span);
        if (tname) *tname = cname;
        return TY_FN;
    }
    Token *t = expect_token(p, TK_IDENT, "a type name");
    static const struct { const char *n; Ty ty; } TYPES[] = {
        {"i8", TY_I8}, {"i16", TY_I16}, {"i32", TY_I32}, {"i64", TY_I64},
        {"u8", TY_U8}, {"u16", TY_U16}, {"u32", TY_U32}, {"u64", TY_U64},
        {"isize", TY_ISIZE}, {"usize", TY_USIZE},
        {"f32", TY_F32}, {"f64", TY_F64}, {"bool", TY_BOOL}, {"str", TY_STR},
        {"()", TY_VOID},
    };
    for (size_t i = 0; i < sizeof TYPES / sizeof TYPES[0]; i++)
        if (strcmp(TYPES[i].n, t->text) == 0) return TYPES[i].ty;
    /* opt<T> / result<T, E> (T3/T4): sugar over built-in anonymous tagged enums.
     * Name convention: tp_<anon> in C; the raw anon name lives in *tname so
     * typecheck/codegen instantiate the same enum shape everywhere. */
    if ((strcmp(t->text, "opt") == 0 || strcmp(t->text, "result") == 0) && at(p, TK_LT)) {
        Ty kind = strcmp(t->text, "result") == 0 ? TY_RESULT : TY_OPT;
        advance(p);                     /* '<' */
        if (p->no_anon) {
            diag(t->span, E0202, SEV_ERROR,
                 "opt/result types are not stored inside struct fields or enum payloads in v0",
                 "put opt/result on fn signatures and let bindings for now");
        }
        Span psp = peek(p)->span;       /* first payload token */
        Ty pt; const char *pn = NULL;
        Ty et = TY_UNSET; const char *en = NULL;
        pt = parse_type(p, &pn);
        Payload pls[2];
        memset(&pls, 0, sizeof pls);
        pls[0].ty = pt;
        pls[0].tname = pn;
        pls[0].span = psp;
        if (kind == TY_RESULT) {
            expect_token(p, TK_COMMA, "',' between result payloads");
            Span esp = peek(p)->span;
            et = parse_type(p, &en);
            pls[1].ty = et;
            pls[1].tname = en;
            pls[1].span = esp;
        }
        expect_token(p, TK_GT, "'>' to close the opt/result payload list");
        /* v0 surface: no nesting, opt carries scalar/struct only */
        if (pt == TY_OPT || pt == TY_RESULT || et == TY_OPT || et == TY_RESULT) {
            diag(psp, E0202, SEV_ERROR, "opt cannot nest v0 (same for result)",
                 "flatten the shape: carry nest-shaped data in a struct");
        }
        if (pt == TY_VOID || et == TY_VOID) {
            diag(psp, E0202, SEV_ERROR, "() payload is not data",
                 "opt/result carry a scalar, str, or struct");
        }
        if (kind == TY_OPT && pt == TY_STR) {
            diag(psp, E0202, SEV_ERROR, "opt<str> is not v0: opt carries a scalar or struct",
                 "store the str on a struct or use result<i32, str> for failure values");
        }
        /* anon enum name built from the payload names before resolution */
        const char *pcan = pt == TY_TYPEDEF ? pn : ty_name(pt);
        char buf[192];
        if (kind == TY_RESULT) {
            const char *ecan = et == TY_TYPEDEF ? en : ty_name(et);
            snprintf(buf, sizeof buf, "result_%s_%s", pcan ? pcan : "?", ecan ? ecan : "?");
        } else {
            snprintf(buf, sizeof buf, "opt_%s", pcan ? pcan : "?");
        }
        const char *name = arena_dupstr(p->a, buf, strlen(buf));
        anon_declare(name, pls, kind == TY_RESULT ? 2 : 1, t->span);
        if (tname) *tname = name;
        return kind;
    }
    if (tname) *tname = t->text;
    return TY_TYPEDEF;
}

/* ---------------- expressions ---------------- */

static Expr *parse_expr(Parser *p);

static Expr *new_expr(Parser *p, ExKind k, Span sp) {
    Expr *e = arena_zalloc(p->a, sizeof(Expr));
    e->kind = k;
    e->span = sp;
    e->ty = TY_UNSET;
    return e;
}

static Expr *parse_primary(Parser *p) {
    Token *t = peek(p);
    switch (t->kind) {
    case TK_INT: {
        Expr *e = new_expr(p, EX_INT, t->span);
        advance(p);
        e->ival = t->ival;
        return e;
    }
    case TK_FLOAT: {
        Expr *e = new_expr(p, EX_FLOAT, t->span);
        advance(p);
        e->fval = t->fval;
        return e;
    }
    case TK_STR: {
        Expr *e = new_expr(p, EX_STR, t->span);
        advance(p);
        e->sval = t->text;
        e->slen = t->len;
        e->ty = TY_STR;
        return e;
    }
    case TK_TRUE:
    case TK_FALSE: {
        Expr *e = new_expr(p, EX_BOOL, t->span);
        advance(p);
        e->bval = t->kind == TK_TRUE;
        e->ty = TY_BOOL;
        return e;
    }
    case TK_IDENT: {
        Expr *e = new_expr(p, EX_IDENT, t->span);
        advance(p);
        e->sval = t->text;
        e->ty = TY_UNSET;
        /* v0 has no null (T3): the keyword does not exist; a bare ident
         * spelled "null" gets the spec diagnostic and no value */
        if (strcmp(t->text, "null") == 0) {
            diag(t->span, E0204, SEV_ERROR,
                 "null and undefined do not exist; use opt (T) for may-be-missing values",
                 "hold the maybe-missing value as opt<T> and match some/none");
            return e;
        }
        /* variant value: Enum::Variant [ ( payloads ) ] */
        if (at(p, TK_COLON2)) {
            advance(p);
            Token *vn = expect_token(p, TK_IDENT, "a variant name after '::'");
            e->kind = EX_VARIANT;
            e->vname = vn->text;
            e->span.len = vn->span.col + vn->span.len - t->span.col;
            if (at(p, TK_LP)) {
                advance(p);
                while (!at(p, TK_RP) && !at(p, TK_EOF)) {
                    Expr **na = realloc(e->args == NULL ? malloc(0) : e->args,
                                        (size_t)(e->nargs + 1) * sizeof(Expr *));
                    if (!na) exit(1);
                    e->args = na;
                    e->args[e->nargs++] = parse_expr(p);
                    if (!eat(p, TK_COMMA)) break;
                }
                expect_token(p, TK_RP, "')' to close the payload values");
            }
            return e;
        }
        /* struct init: Ident { inits, ... } (suppressed where a block may follow an expression) */
        if (at(p, TK_BRACE_L) && p->si_ok) {
            e->kind = EX_STRUCTINIT;
            advance(p);
            while (!at(p, TK_BRACE_R) && !at(p, TK_EOF)) {
                Token *fn = expect_token(p, TK_IDENT, "a field name in the struct init");
                const char **na = realloc(e->inames == NULL ? malloc(0) : e->inames,
                                          (size_t)(e->nargs + 1) * sizeof(char *));
                Expr **na2 = realloc(e->args == NULL ? malloc(0) : e->args,
                                     (size_t)(e->nargs + 1) * sizeof(Expr *));
                if (!na || !na2) exit(1);
                e->inames = na;
                e->args = na2;
                e->inames[e->nargs] = fn->text;
                if (eat(p, TK_COLON)) e->args[e->nargs++] = parse_expr(p);
                else {  /* shorthand { x } uses the binding x */
                    Expr *sh = new_expr(p, EX_IDENT, fn->span);
                    sh->sval = fn->text;
                    e->args[e->nargs++] = sh;
                }
                if (!eat(p, TK_COMMA)) break;
            }
            expect_token(p, TK_BRACE_R, "'}' to close the struct init");
            return e;
        }
        /* call: ident ( args ) */
        if (at(p, TK_LP)) {
            advance(p);
            e->kind = EX_CALL;
            e->callee = e->sval;
            while (!at(p, TK_RP) && !at(p, TK_EOF)) {
                Expr **na = realloc(e->args == NULL ? malloc(0) : e->args,
                                    (size_t)(e->nargs + 1) * sizeof(Expr *));
                if (!na) exit(1);
                e->args = na;
                e->args[e->nargs++] = parse_expr(p);
                if (!eat(p, TK_COMMA)) break;
            }
            expect_token(p, TK_RP, "')' to close the call");
        }
        return e;
    }
    case TK_CAST: {
        /* the one conversion builtin: cast<T>(expr); target types are v0 numeric only */
        Expr *e = new_expr(p, EX_CAST, t->span);
        advance(p);
        expect_token(p, TK_LT, "'<' to open the cast target");
        e->ty = parse_type(p, &e->sval);
        expect_token(p, TK_GT, "'>' to close the cast target");
        expect_token(p, TK_LP, "'(' to open the cast operand");
        e->operand = parse_expr(p);
        expect_token(p, TK_RP, "')' to close the cast operand");
        /* diag span covers the whole call: cast keyword through ')' */
        Token *close = peekn(p, -1);
        if (close->span.line == t->span.line)
            e->span.len = close->span.col + close->span.len - t->span.col;
        return e;
    }
    case TK_MATCH: {
        diag(t->span, E0101, SEV_ERROR, "match as an expression lands in a later slice",
             "match is a statement in P1.1; bind results to a let inside the arms");
        advance(p);
        return new_expr(p, EX_INT, t->span);
    }
    case TK_LP: {
        advance(p);
        Expr *e = parse_expr(p);
        expect_token(p, TK_RP, "')' to close the group");
        return e;
    }
    default: {
        Span sp = t->span;
        char msg[120];
        snprintf(msg, sizeof msg, "expected an expression, got %s", tok_kind_word(t->kind));
        diag(sp, E0101, SEV_ERROR, msg, "primary forms: literal, ident, call, (expr)");
        advance(p);
        return new_expr(p, EX_INT, sp);
    }
    }
}

static Expr *parse_unary(Parser *p) {
    Token *t = peek(p);
    if (t->kind == TK_NOT || t->kind == TK_MINUS || t->kind == TK_AMP) {
        Expr *e = new_expr(p, EX_UN, t->span);
        advance(p);
        e->unop = t->kind == TK_NOT ? UN_NOT : t->kind == TK_MINUS ? UN_NEG : UN_ADDR;
        if (e->unop == UN_ADDR) {
            diag(t->span, E0101, SEV_ERROR, "'&' address-of arrives with borrows (P1.1+)",
                 "pointer-free core until borrow rules land");
        }
        e->operand = parse_unary(p);
        return e;
    }
    /* postfix: primary, then chains */
    Expr *e = parse_primary(p);
    for (;;) {
        if (at(p, TK_DOT)) {
            advance(p);
            Token *fn = expect_token(p, TK_IDENT, "a field name after '.'");
            Expr *f = new_expr(p, EX_FIELD, e->span);
            f->base = e;
            f->sval = fn->text;
            f->span.len = fn->span.col + fn->span.len - e->span.col;
            if (at(p, TK_LP)) {
                diag(fn->span, E0101, SEV_ERROR, "methods are not a thing in v0",
                     "fields are plain data; move the logic into a fn");
            }
            e = f;
            continue;
        }
        if (at(p, TK_LB)) {
            advance(p);
            Expr *ix = new_expr(p, EX_INDEX, e->span);
            ix->base = e;
            ix->index = parse_expr(p);
            Token *rb = expect_token(p, TK_RB, "']' to close the index");
            if (rb->span.line == e->span.line)
                ix->span.len = rb->span.col + rb->span.len - e->span.col;
            e = ix;
            continue;
        }
        /* spread `?` (T4): lowest-forced postfix, opt/result unwrap-propagate */
        if (at(p, TK_QUESTION)) {
            Token *q = advance(p);
            Expr *s = new_expr(p, EX_SPREAD, e->span);
            s->operand = e;
            if (q->span.line == e->span.line)
                s->span.len = q->span.col + q->span.len - e->span.col;
            e = s;
            continue;
        }
        break;
    }
    return e;
}

static Expr *parse_binary(Parser *p, int min_prec) {
    Expr *lhs = parse_unary(p);
    for (;;) {
        TokKind k = peek(p)->kind;
        int prec = -1;
        bool right_assoc = false;
        switch (k) {
        case TK_OR: prec = 1; break;
        case TK_AND: prec = 2; break;
        case TK_EQ: case TK_NE: prec = 3; break;
        case TK_LT: case TK_GT: case TK_LE: case TK_GE: prec = 4; break;
        case TK_PLUS: case TK_MINUS: prec = 5; break;
        case TK_STAR: case TK_SLASH: case TK_PERCENT: prec = 6; break;
        case TK_POW: prec = 7; right_assoc = true; break;
        default: break;
        }
        if (prec < min_prec || prec < 0) break;
        Token *op = advance(p);
        (void)op;
        Expr *rhs = parse_binary(p, right_assoc ? prec : prec + 1);
        Expr *e = new_expr(p, EX_BIN, op->span);
        e->op = k;
        e->lhs = lhs;
        e->rhs = rhs;
        /* diag span covers the whole operator expression (same line) */
        e->span = lhs->span;
        if (rhs->span.line == lhs->span.line)
            e->span.len = rhs->span.col + rhs->span.len - lhs->span.col;
        lhs = e;
    }
    return lhs;
}

static Expr *parse_expr(Parser *p) { return parse_binary(p, 1); }

/* ---------------- statements ---------------- */

static Stmt *parse_stmt(Parser *p);

static void push_stmt(Stmt ***arr, int *n, Stmt *s, Arena *a) {
    Stmt **na = arena_alloc(a, sizeof(Stmt *) * (size_t)(*n + 1));
    if (*n) memcpy(na, *arr, sizeof(Stmt *) * (size_t)*n);
    na[*n] = s;
    *arr = na;
    (*n)++;
}

static Stmt *new_stmt(Parser *p, StKind k, Span sp) {
    Stmt *s = arena_zalloc(p->a, sizeof(Stmt));
    s->kind = k;
    s->span = sp;
    return s;
}

static Stmt *parse_block_stmt(Parser *p);  /* always returns a ST_BLOCK */

/* conditions and match scrutinees: `ident {` would be ambiguous with the
 * following block, so struct inits are suppressed there (parenthesize instead) */
static Expr *parse_cond_expr(Parser *p) {
    int save = p->si_ok;
    p->si_ok = 0;
    Expr *e = parse_expr(p);
    p->si_ok = save;
    return e;
}

static Stmt *parse_if(Parser *p) {
    Token *ifkw = advance(p); /* if */
    Stmt *s = new_stmt(p, ST_IF, ifkw->span);
    s->cond = parse_cond_expr(p);
    Stmt *blk = parse_block_stmt(p);
    s->body = blk->body;
    s->nbody = blk->nbody;
    if (eat(p, TK_ELSE)) {
        if (at(p, TK_IF)) s->els = parse_if(p);
        else s->els = parse_block_stmt(p);
    }
    return s;
}

static Stmt *parse_while(Parser *p) {
    Token *kw = advance(p);
    Stmt *s = new_stmt(p, ST_WHILE, kw->span);
    s->cond = parse_cond_expr(p);
    Stmt *blk = parse_block_stmt(p);
    s->body = blk->body;
    s->nbody = blk->nbody;
    return s;
}

/* ---------------- match ---------------- */

static void parse_pattern(Parser *p, MatchArm *arm) { /* fills arm pattern fields */
    Token *t = peek(p);
    arm->span = t->span;
    if (t->kind == TK_INT) { arm->pkind = PAT_LIT_INT; arm->ival = t->ival; advance(p); return; }
    if (t->kind == TK_TRUE || t->kind == TK_FALSE) {
        arm->pkind = PAT_LIT_BOOL; arm->bval = t->kind == TK_TRUE; advance(p); return;
    }
    if (t->kind != TK_IDENT) {
        char msg[120];
        advance(p);
        snprintf(msg, sizeof msg, "unsupported pattern form, got %s", tok_kind_word(t->kind));
        diag(t->span, E0101, SEV_ERROR, msg, "patterns: literal, variant, '_' wildcards");
        return;
    }
    advance(p);
    if (strcmp(t->text, "_") == 0) {    /* wildcard */
        arm->pkind = PAT_WILD;
        return;
    }
    arm->pkind = PAT_VARIANT;
    if (at(p, TK_COLON2)) {
        advance(p);
        arm->ename = t->text;
        Token *vn = expect_token(p, TK_IDENT, "a variant name after '::'");
        arm->vname = vn->text;
        arm->span.len = vn->span.col + vn->span.len - t->span.col;
    } else {
        arm->ename = NULL;              /* bare: resolved against the scrutinee */
        arm->vname = t->text;
        arm->span.len = t->span.len;
    }
    if (at(p, TK_LP)) {
        advance(p);
        while (!at(p, TK_RP) && !at(p, TK_EOF)) {
            Token *bn = expect_token(p, TK_IDENT, "a pattern binding name");
            const char **na = realloc(arm->binds == NULL ? malloc(0) : arm->binds,
                                      (size_t)(arm->nbinds + 1) * sizeof(char *));
            if (!na) exit(1);
            arm->binds = na;
            arm->binds[arm->nbinds++] = bn->text;
            if (!eat(p, TK_COMMA)) break;
        }
        expect_token(p, TK_RP, "')' to close the pattern bindings");
    }
    return;
}

static Stmt *parse_match(Parser *p) {
    Token *kw = advance(p);
    Stmt *s = new_stmt(p, ST_MATCH, kw->span);
    s->cond = parse_cond_expr(p);
    expect_token(p, TK_BRACE_L, "'{' to open the match arms");
    while (!at(p, TK_BRACE_R) && !at(p, TK_EOF)) {
        MatchArm *arm = arena_zalloc(p->a, sizeof(MatchArm));
        parse_pattern(p, arm);
        expect_token(p, TK_FATARROW, "'=>' between pattern and arm");
        Stmt *blk = parse_block_stmt(p);
        arm->body = blk->body;
        arm->nbody = blk->nbody;
        MatchArm **na = arena_alloc(p->a, sizeof(MatchArm *) * (size_t)(s->narms + 1));
        if (s->narms) memcpy(na, s->arms, sizeof(MatchArm *) * (size_t)s->narms);
        na[s->narms++] = arm;
        s->arms = na;
        eat(p, TK_COMMA);               /* comma between arms is optional; blocks are unambiguous */
    }
    expect_token(p, TK_BRACE_R, "'}' to close the match arm list");
    return s;
}

static Stmt *parse_var_decl(Parser *p) {
    Token *kw = advance(p); /* let | const */
    Stmt *s = new_stmt(p, ST_LET, kw->span);
    s->is_const = kw->kind == TK_CONST;
    s->ty = TY_UNSET;          /* zalloc is 0; TY_I8 is 0 - be explicit */
    Token *name = expect_token(p, TK_IDENT, "a binding name after let/const");
    s->name = name->text;
    s->span = kw->span;
    if (eat(p, TK_COLON)) s->ty = parse_type(p, &s->tname);
    if (eat(p, TK_ASSIGN)) s->init = parse_expr(p);
    expect_token(p, TK_SEMI, "';' to end the statement");
    return s;
}

static Stmt *parse_stmt(Parser *p) {
    Token *t = peek(p);
    switch (t->kind) {
    case TK_LET:
    case TK_CONST:
        return parse_var_decl(p);
    case TK_RETURN: {
        advance(p);
        Stmt *s = new_stmt(p, ST_RETURN, t->span);
        if (!at(p, TK_SEMI)) s->value = parse_expr(p);
        expect_token(p, TK_SEMI, "';' after return");
        return s;
    }
    case TK_IF:
        return parse_if(p);
    case TK_WHILE:
        return parse_while(p);
    case TK_BRACE_L:
        return parse_block_stmt(p);
    case TK_MATCH:
        return parse_match(p);
    case TK_SEMI:  /* empty statement: allowed, no-op */
        advance(p);
        return new_stmt(p, ST_BLOCK, t->span);
    default: {
        Expr *e = parse_expr(p);
        if (peek(p)->kind == TK_ASSIGN || peek(p)->kind == TK_ADDEQ ||
            peek(p)->kind == TK_SUBEQ || peek(p)->kind == TK_MULEQ ||
            peek(p)->kind == TK_DIVEQ || peek(p)->kind == TK_MODEQ) {
            Token *op = advance(p);
            Stmt *s = new_stmt(p, ST_ASSIGN, e->span);
            s->target = e;
            s->aop = op->kind;
            s->value = parse_expr(p);
            expect_token(p, TK_SEMI, "';' to end the statement");
            return s;
        }
        expect_token(p, TK_SEMI, "';' to end the statement");
        Stmt *s = new_stmt(p, ST_EXPR, e->span);
        s->value = e;
        return s;
    }
    }
}

static Stmt *parse_block_stmt(Parser *p) {
    expect_token(p, TK_BRACE_L, "'{'");
    Stmt *s = new_stmt(p, ST_BLOCK, peekn(p, -1)->span);
    while (!at(p, TK_BRACE_R) && !at(p, TK_EOF)) {
        push_stmt(&s->body, &s->nbody, parse_stmt(p), p->a);
    }
    expect_token(p, TK_BRACE_R, "'}' or statement");
    return s;
}

/* ---------------- top level ---------------- */

static FnDecl *parse_fn_proto(Parser *p) {
    Token *kw = expect_token(p, TK_FN, "'fn'");
    Token *name = expect_token(p, TK_IDENT, "a function name");
    FnDecl *fn = arena_zalloc(p->a, sizeof(FnDecl));
    fn->name = name->text;
    fn->span = kw->span;
    expect_token(p, TK_LP, "'(' after fn name");
    while (!at(p, TK_RP) && !at(p, TK_EOF)) {
        Token *pn = expect_token(p, TK_IDENT, "a parameter name");
        expect_token(p, TK_COLON, "':' before the parameter type");
        Param *np = arena_alloc(p->a, sizeof(Param));
        np->name = pn->text;
        np->span = pn->span;
        np->ty = parse_type(p, &np->tname);
        Param *na = realloc(fn->params == NULL ? malloc(0) : fn->params,
                            sizeof(Param) * (size_t)(fn->nparams + 1));
        if (!na) exit(1);
        fn->params = na;
        fn->params[fn->nparams++] = *np;
        if (!eat(p, TK_COMMA)) break;
    }
    expect_token(p, TK_RP, "')' to close parameters");
    if (eat(p, TK_ARROW)) fn->ret = parse_type(p, &fn->retname);
    else fn->ret = TY_VOID;
    return fn;
}

static EnDecl *parse_enum(Parser *p) {
    Token *kw = advance(p);  /* enum */
    EnDecl *en = arena_zalloc(p->a, sizeof(EnDecl));
    Token *name = expect_token(p, TK_IDENT, "an enum name");
    en->name = name->text;
    en->span = kw->span;
    /* generics <T> arrive later: reject with a clear shape error */
    expect_token(p, TK_BRACE_L, "'{' to open the enum variants");
    while (!at(p, TK_BRACE_R) && !at(p, TK_EOF)) {
        Token *vn = expect_token(p, TK_IDENT, "a variant name");
        Variant *v = arena_alloc(p->a, sizeof(Variant));
        v->name = vn->text;
        v->span = vn->span;
        if (eat(p, TK_LP)) {
            while (!at(p, TK_RP) && !at(p, TK_EOF)) {
                Payload *pl = arena_alloc(p->a, sizeof(Payload));
                p->no_anon = 1;
                pl->ty = parse_type(p, &pl->tname);
                p->no_anon = 0;
                pl->span = peekn(p, -1)->span;
                Payload *na = realloc(v->payloads == NULL ? malloc(0) : v->payloads,
                                      (size_t)(v->npayloads + 1) * sizeof(Payload));
                if (!na) exit(1);
                v->payloads = na;
                v->payloads[v->npayloads++] = *pl;
                if (!eat(p, TK_COMMA)) break;
            }
            expect_token(p, TK_RP, "')' to close the payload types");
        }
        Variant *na = realloc(en->variants == NULL ? malloc(0) : en->variants,
                              (size_t)(en->nvariants + 1) * sizeof(Variant));
        if (!na) exit(1);
        en->variants = na;
        en->variants[en->nvariants++] = *v;
        if (!eat(p, TK_COMMA)) break;   /* comma between variants */
    }
    expect_token(p, TK_BRACE_R, "'}' to close the enum");
    return en;
}

static StDecl *parse_struct(Parser *p) {
    Token *kw = advance(p);  /* struct */
    StDecl *st = arena_zalloc(p->a, sizeof(StDecl));
    Token *name = expect_token(p, TK_IDENT, "a struct name");
    st->name = name->text;
    st->span = kw->span;
    expect_token(p, TK_BRACE_L, "'{' to open the struct fields");
    while (!at(p, TK_BRACE_R) && !at(p, TK_EOF)) {
        Token *fn = expect_token(p, TK_IDENT, "a field name");
        expect_token(p, TK_COLON, "':' before the field type");
        StField *f = arena_alloc(p->a, sizeof(StField));
        f->name = fn->text;
        f->span = fn->span;
        p->no_anon = 1;
        f->ty = parse_type(p, &f->tname);
        p->no_anon = 0;
        expect_token(p, TK_SEMI, "';' after each field");
        StField *na = realloc(st->fields == NULL ? malloc(0) : st->fields,
                              (size_t)(st->nfields + 1) * sizeof(StField));
        if (!na) exit(1);
        st->fields = na;
        st->fields[st->nfields++] = *f;
    }
    expect_token(p, TK_BRACE_R, "'}' to close the struct");
    return st;
}

Decl **parse_file(Arena *a, Token *toks, int ntoks, const char *file) {
    Parser p;
    memset(&p, 0, sizeof p);
    p.toks = toks;
    p.ntoks = ntoks;
    p.a = a;
    p.file = file;
    p.si_ok = 1;               /* struct init allowed by default; conditions suppress */

    VecDecl out;
    memset(&out, 0, sizeof out);

    /* shebang line: ignore a #! prefix (lexer skips to first real token) */

    while (!at(&p, TK_EOF)) {
        bool is_pub = false;
        if (at(&p, TK_PUB)) {
            advance(&p);
            is_pub = true;
        }
        if (at(&p, TK_USE)) {
            Token *usekw = advance(&p);
            if (at(&p, TK_STR)) {
                /* module import: use "path.tp" as alias; */
                Token *lit = advance(&p);
                Decl *d = arena_zalloc(a, sizeof(Decl));
                d->kind = D_USEMOD;
                d->path = arena_dupstr(a, lit->text, lit->len);
                d->span = usekw->span;
                if (eat(&p, TK_AS)) {
                    Token *an = expect_token(&p, TK_IDENT, "an alias name after as");
                    d->name = an->text;
                } else {
                    diag(lit->span, E0101, SEV_ERROR,
                         "module import needs an alias: use \"path.tp\" as name;",
                         "name the module so qualified calls read alias::fn");
                    d->name = "module";
                }
                expect_token(&p, TK_SEMI, "';' after module import");
                vec_push_ptr((VecPtr *)&out, d);
                continue;
            }
            if (is_pub) {
                diag(usekw->span, E0101, SEV_ERROR, "'pub' applies to fn/struct/enum/const",
                     "module imports are not exported");
            }
            expect_token(&p, TK_TIER, "'tier' after use");
            Token *tname = expect_token(&p, TK_IDENT, "a tier name (kernel|core|std|full)");
            /* tier check: parsed but honored in P1.1 module model; record now */
            Decl *d = arena_zalloc(a, sizeof(Decl));
            d->kind = D_TIER;
            d->name = tname->text;
            d->span = usekw->span;
            vec_push_ptr((VecPtr *)&out, d);
            expect_token(&p, TK_SEMI, "';' after tier name");
            continue;
        }
        if (at(&p, TK_LET) || at(&p, TK_CONST)) {
            Token *kw = advance(&p);
            Decl *d = arena_zalloc(a, sizeof(Decl));
            d->kind = D_LET;
            d->is_pub = is_pub;
            d->is_const = (kw->kind == TK_CONST);
            Token *name = expect_token(&p, TK_IDENT, "a binding name after let/const");
            d->name = name->text;
            d->span = kw->span;
            if (eat(&p, TK_COLON)) d->ty = parse_type(&p, &d->tname);
            else d->ty = TY_UNSET;
            if (eat(&p, TK_ASSIGN)) d->init = parse_expr(&p);
            expect_token(&p, TK_SEMI, "';' to end the declaration");
            vec_push_ptr((VecPtr *)&out, d);
            continue;
        }
        if (at(&p, TK_FN)) {
            FnDecl *fn = parse_fn_proto(&p);
            fn->body = NULL;
            fn->nbody = 0;
            Stmt *blk = parse_block_stmt(&p);
            fn->body = blk->body;
            fn->nbody = blk->nbody;
            Decl *d = arena_zalloc(a, sizeof(Decl));
            d->kind = D_FN;
            d->is_pub = is_pub;
            d->fn = fn;
            vec_push_ptr((VecPtr *)&out, d);
            continue;
        }
        if (at(&p, TK_STRUCT)) {
            StDecl *st = parse_struct(&p);
            Decl *d = arena_zalloc(a, sizeof(Decl));
            d->kind = D_STRUCT;
            d->is_pub = is_pub;
            d->st = st;
            vec_push_ptr((VecPtr *)&out, d);
            continue;
        }
        if (at(&p, TK_ENUM)) {
            EnDecl *en = parse_enum(&p);
            Decl *d = arena_zalloc(a, sizeof(Decl));
            d->kind = D_ENUM;
            d->is_pub = is_pub;
            d->en = en;
            vec_push_ptr((VecPtr *)&out, d);
            continue;
        }
        if (is_pub) {
            diag(peek(&p)->span, E0101, SEV_ERROR,
                 "'pub' must be followed by fn/struct/enum/const",
                 "drop it or export an actual declaration");
        }
        Span sp = peek(&p)->span;
        char msg[160];
        snprintf(msg, sizeof msg, "expected a top-level declaration, got %s", tok_kind_word(peek(&p)->kind));
        diag(sp, E0101, SEV_ERROR, msg, "top level: use tier, fn, struct, enum, const");
        break;
    }

    vec_push_ptr((VecPtr *)&out, NULL);   /* NULL-terminate for the driver */
    return (Decl **)out.data;
}
