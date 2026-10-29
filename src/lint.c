/* lint.c - tier linter: a file's declared tier is a permission ceiling.
 *
 * Parses only (no typecheck), walks the AST and reports features used above
 * the declared tier as E0301. A file with no `use tier` declaration is treated
 * as `core`, matching the language default for single-file programs.
 *
 * Feature ladder (v0 surface):
 *   kernel (0): ints, bools, structs, enums, fn, fixed arrays, const
 *   core   (1): + str, opt, result, match, ?
 *   std    (2): + closures, generics (no syntax yet)
 *   full   (3): + async (no syntax yet)
 */
#include "common.h"

static int tier_level(const char *name) {
    if (!name) return -1;
    if (strcmp(name, "kernel") == 0) return 0;
    if (strcmp(name, "core") == 0) return 1;
    if (strcmp(name, "std") == 0) return 2;
    if (strcmp(name, "full") == 0) return 3;
    return -1;
}

static const char *tier_name(int lvl) {
    switch (lvl) {
    case 0: return "kernel";
    case 1: return "core";
    case 2: return "std";
    case 3: return "full";
    default: return "?";
    }
}

static void need_tier(int cur, int req, const char *feat, Span sp) {
    if (cur < 0 || cur >= req) return;
    char msg[180];
    snprintf(msg, sizeof msg, "feature [%s] requires tier %d; current tier is %d %s",
             feat, req, cur, tier_name(cur));
    diag(sp, E0301, SEV_ERROR, msg,
         "raise the use tier ceiling or rewrite the file without this feature");
}

static void lint_ty(Ty t, const char *tname, int cur, Span sp) {
    switch (t) {
    case TY_STR: need_tier(cur, 1, "str", sp); break;
    case TY_OPT: need_tier(cur, 1, "opt", sp); break;
    case TY_RESULT: need_tier(cur, 1, "result", sp); break;
    case TY_ARRAY: {
        if (!tname) break;
        ArrayInfo *ai = array_find(tname);
        if (ai) lint_ty(ai->elem_ty, ai->elem_tname, cur, sp);
        break;
    }
    default: break;
    }
}

static void lint_expr(Expr *e, int cur);

static void lint_exprs(Expr **xs, int n, int cur) {
    for (int i = 0; i < n; i++) lint_expr(xs[i], cur);
}

static void lint_expr(Expr *e, int cur) {
    if (!e) return;
    lint_ty(e->ty, e->tname, cur, e->span);
    switch (e->kind) {
    case EX_SPREAD: need_tier(cur, 1, "?", e->span); break;
    case EX_IDENT:
    case EX_INT:
    case EX_FLOAT:
    case EX_STR:
    case EX_BOOL:
        break;
    case EX_BIN:
        lint_expr(e->lhs, cur);
        lint_expr(e->rhs, cur);
        break;
    case EX_UN:
    case EX_CAST:
        lint_expr(e->operand, cur);
        break;
    case EX_CALL:
        lint_exprs(e->args, e->nargs, cur);
        break;
    case EX_INDEX:
        lint_expr(e->base, cur);
        lint_expr(e->index, cur);
        break;
    case EX_FIELD:
        lint_expr(e->base, cur);
        break;
    case EX_STRUCTINIT:
    case EX_VARIANT:
        lint_exprs(e->args, e->nargs, cur);
        break;
    }
}

static void lint_stmts(Stmt **ss, int n, int cur);

static void lint_stmt(Stmt *s, int cur) {
    if (!s) return;
    switch (s->kind) {
    case ST_LET:
        lint_ty(s->ty, s->tname, cur, s->span);
        lint_expr(s->init, cur);
        break;
    case ST_ASSIGN:
        lint_expr(s->target, cur);
        lint_expr(s->value, cur);
        break;
    case ST_RETURN:
        lint_expr(s->value, cur);
        break;
    case ST_IF:
        lint_expr(s->cond, cur);
        lint_stmts(s->body, s->nbody, cur);
        lint_stmt(s->els, cur);
        break;
    case ST_WHILE:
        lint_expr(s->cond, cur);
        lint_stmts(s->body, s->nbody, cur);
        break;
    case ST_MATCH:
        need_tier(cur, 1, "match", s->span);
        lint_expr(s->cond, cur);
        for (int i = 0; i < s->narms; i++) {
            MatchArm *a = s->arms[i];
            if (!a) continue;
            lint_stmts(a->body, a->nbody, cur);
        }
        break;
    case ST_EXPR:
        lint_expr(s->value, cur);
        break;
    case ST_BLOCK:
        lint_stmts(s->body, s->nbody, cur);
        break;
    }
}

static void lint_stmts(Stmt **ss, int n, int cur) {
    for (int i = 0; i < n; i++) lint_stmt(ss[i], cur);
}

void lint_file(Arena *a, Decl **decls, int ndecls) {
    (void)a;
    int cur = 1;   /* default tier for a single-file program */
    for (int i = 0; i < ndecls; i++)
        if (decls[i] && decls[i]->kind == D_TIER) {
            int lvl = tier_level(decls[i]->name);
            if (lvl >= 0) cur = lvl;
        }

    for (int i = 0; i < ndecls; i++) {
        Decl *d = decls[i];
        if (!d) continue;
        switch (d->kind) {
        case D_FN:
            if (!d->fn) break;
            lint_ty(d->fn->ret, d->fn->retname, cur, d->fn->span);
            for (int k = 0; k < d->fn->nparams; k++)
                lint_ty(d->fn->params[k].ty, d->fn->params[k].tname, cur,
                        d->fn->params[k].span);
            lint_stmts(d->fn->body, d->fn->nbody, cur);
            break;
        case D_LET:
            lint_ty(d->ty, d->tname, cur, d->span);
            lint_expr(d->init, cur);
            break;
        case D_STRUCT:
            if (!d->st) break;
            for (int k = 0; k < d->st->nfields; k++)
                lint_ty(d->st->fields[k].ty, d->st->fields[k].tname, cur,
                        d->st->fields[k].span);
            break;
        case D_ENUM:
            if (!d->en) break;
            for (int v = 0; v < d->en->nvariants; v++)
                for (int p = 0; p < d->en->variants[v].npayloads; p++)
                    lint_ty(d->en->variants[v].payloads[p].ty,
                            d->en->variants[v].payloads[p].tname, cur,
                            d->en->variants[v].payloads[p].span);
            break;
        default:
            break;
        }
    }
}
