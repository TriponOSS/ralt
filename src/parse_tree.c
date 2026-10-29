/* parse_tree.c - the frozen P3.1 oracle: dumps the post-parse AST in a flat,
 * prefix, byte-deterministic form. The self-host parser port (selfhost/tp
 * parser) must reproduce it token for token, exactly like selfhost/lexer.tp
 * does for `ralt tokens`. Spans stay out of the dump: the guard posts它们 via
 * the tokens oracle; the tree oracle guards SHAPE.
 * Format contract (same in C and Tripon):
 *   - decls at indent 0, each node = one line, two-space indent per level
 *   - statements: FN/STRUCT/ENUM/TIER/USE/LET/... ; expressions inline prefix
 *   - expr atoms: INT <v> | FLOAT | STR | BOOL <b> | VAR <n>
 *   - expr groups: (BIN<opword> l r) | (UN<opword> e) | (CALL<name> a...)
 *     | (INDEX b i) | (FIELD b <name>) | (INIT t i ...) | (CAST t e)
 *     | (VINST <vname>) | (SPREAD e)
 *   - never print symbol names that come from resolution; ty words from
 *     ty_name() only */
#include "common.h"
#include <stdio.h>

static void put_word(FILE *o, const char *s) {
    fprintf(o, "%s", s ? s : "?");
}

/* prefix expr; single line, no trailing newline */
static void dump_expr(FILE *o, Expr *e, int ind) {
    if (!e) { fprintf(o, "-"); return; }
    switch (e->kind) {
    case EX_INT:
        fprintf(o, "INT %lld", e->ival);
        break;
    case EX_FLOAT:
        fprintf(o, "FLOAT");
        break;
    case EX_STR:
        fprintf(o, "STR");
        break;
    case EX_BOOL:
        fprintf(o, "BOOL %s", e->bval ? "true" : "false");
        break;
    case EX_IDENT:
        put_word(o, "VAR ");
        put_word(o, e->sval);
        break;
    case EX_BIN:
        fputc('(', o);
        put_word(o, "BIN");
        fputc(' ', o);
        put_word(o, tok_kind_word(e->op));
        fputc(' ', o);
        dump_expr(o, e->lhs, ind);
        fputc(' ', o);
        dump_expr(o, e->rhs, ind);
        fputc(')', o);
        break;
    case EX_UN:
        fputc('(', o);
        put_word(o, "UN");
        fputc(' ', o);
        put_word(o, tok_kind_word(e->unop == UN_NOT ? TK_NOT : TK_MINUS));
        fputc(' ', o);
        dump_expr(o, e->operand, ind);
        fputc(')', o);
        break;
    case EX_CALL:
        fputc('(', o);
        put_word(o, "CALL");
        fputc(' ', o);
        put_word(o, e->callee);
        for (int i = 0; i < e->nargs; i++) {
            fputc(' ', o);
            dump_expr(o, e->args[i], ind);
        }
        fputc(')', o);
        break;
    case EX_INDEX:
        fputc('(', o);
        put_word(o, "INDEX");
        fputc(' ', o);
        dump_expr(o, e->base, ind);
        fputc(' ', o);
        dump_expr(o, e->index, ind);
        fputc(')', o);
        break;
    case EX_FIELD:
        fputc('(', o);
        put_word(o, "FIELD");
        fputc(' ', o);
        dump_expr(o, e->base, ind);
        fputc(' ', o);
        put_word(o, e->sval);
        fputc(')', o);
        break;
    case EX_STRUCTINIT:
        fputc('(', o);
        put_word(o, "INIT");
        fputc(' ', o);
        put_word(o, e->sval);
        for (int i = 0; i < e->nargs; i++) {
            fputc(' ', o);
            put_word(o, e->inames[i]);
            fputc('=', o);
            dump_expr(o, e->args[i], ind);
        }
        fputc(')', o);
        break;
    case EX_VARIANT:
        fputc('(', o);
        put_word(o, e->bare_ctor ? "VCT" : "VINST");
        fputc(' ', o);
        put_word(o, e->sval);
        if (!e->bare_ctor) {
            fputc(' ', o);
            put_word(o, e->vname);
        }
        for (int i = 0; i < e->nargs; i++) {
            fputc(' ', o);
            dump_expr(o, e->args[i], ind);
        }
        fputc(')', o);
        break;
    case EX_CAST:
        fputc('(', o);
        put_word(o, "CAST");
        fputc(' ', o);
        put_word(o, e->sval);
        fputc(' ', o);
        dump_expr(o, e->operand, ind);
        fputc(')', o);
        break;
    case EX_SPREAD:
        fputc('(', o);
        put_word(o, "SPREAD");
        fputc(' ', o);
        dump_expr(o, e->operand, ind);
        fputc(')', o);
        break;
    }
}

static void indent(FILE *o, int n) {
    for (int i = 0; i < n; i++) fputs("  ", o);
}

static void dump_ty_annot(FILE *o, Ty t, const char *tnm) {
    if (t == TY_UNSET) { put_word(o, "?"); return; }
    put_word(o, ty_name(t));
    if ((t == TY_STRUCT || t == TY_ENUM || t == TY_TYPEDEF) && tnm) {
        fputc(' ', o);
        put_word(o, tnm);
    }
}

static void dump_stmt(FILE *o, Stmt *s, int ind) {
    if (!s) return;
    indent(o, ind);
    switch (s->kind) {
    case ST_LET:
        put_word(o, "LET ");
        put_word(o, s->name);
        if (s->ty != TY_UNSET) {
            put_word(o, " ty=");
            dump_ty_annot(o, s->ty, s->tname);
        }
        if (s->init) {
            put_word(o, " =");
            fputc(' ', o);
            dump_expr(o, s->init, ind);
        }
        fputc('\n', o);
        break;
    case ST_ASSIGN:
        put_word(o, "ASSIGN ");
        put_word(o, tok_kind_word(s->aop));
        fputc(' ', o);
        dump_expr(o, s->target, ind);
        fputc(' ', o);
        dump_expr(o, s->value, ind);
        fputc('\n', o);
        break;
    case ST_RETURN:
        put_word(o, "RETURN");
        if (s->value) {
            fputc(' ', o);
            dump_expr(o, s->value, ind);
        }
        fputc('\n', o);
        break;
    case ST_IF:
        put_word(o, "IF");
        fputc(' ', o);
        dump_expr(o, s->cond, ind);
        fputc('\n', o);
        for (int i = 0; i < s->nbody; i++) dump_stmt(o, s->body[i], ind + 1);
        if (s->els) {
            indent(o, ind);
            fputs("ELSE\n", o);
            dump_stmt(o, s->els, ind + 1);
        }
        break;
    case ST_WHILE:
        put_word(o, "WHILE");
        fputc(' ', o);
        dump_expr(o, s->cond, ind);
        fputc('\n', o);
        for (int i = 0; i < s->nbody; i++) dump_stmt(o, s->body[i], ind + 1);
        break;
    case ST_MATCH:
        put_word(o, "MATCH");
        fputc(' ', o);
        dump_expr(o, s->cond, ind);
        fputc('\n', o);
        for (int a = 0; a < s->narms; a++) {
            MatchArm *m = s->arms[a];
            indent(o, ind + 1);
            put_word(o, "ARM");
            fputc(' ', o);
            switch (m->pkind) {
            case PAT_WILD: fputs("_", o); break;
            case PAT_LIT_INT: fprintf(o, "INT %lld", m->ival); break;
            case PAT_LIT_BOOL: fprintf(o, "BOOL %s", m->bval ? "true" : "false"); break;
            case PAT_VARIANT:
                put_word(o, "VARPAT");
                fputc(' ', o);
                put_word(o, m->ename ? m->ename : "-");
                fputc(' ', o);
                put_word(o, m->vname);
                break;
            }
            for (int b = 0; b < m->nbinds; b++) {
                fputc(' ', o);
                put_word(o, m->binds[b]);
            }
            fputc('\n', o);
            for (int i = 0; i < m->nbody; i++) dump_stmt(o, m->body[i], ind + 2);
        }
        break;
    case ST_EXPR:
        put_word(o, "EXPR");
        fputc(' ', o);
        dump_expr(o, s->value, ind);
        fputc('\n', o);
        break;
    case ST_BLOCK:
        fputs("BLOCK\n", o);
        for (int i = 0; i < s->nbody; i++) dump_stmt(o, s->body[i], ind + 1);
        break;
    }
}

void parse_tree_dump(FILE *o, Decl **decls, int ndecls) {
    for (int d = 0; d < ndecls; d++) {
        Decl *dl = decls[d];
        switch (dl->kind) {
        case D_FN:
            put_word(o, "FN ");
            put_word(o, dl->fn->name);
            put_word(o, " ret=");
            dump_ty_annot(o, dl->fn->ret, dl->fn->retname);
            fputc('\n', o);
            for (int i = 0; i < dl->fn->nparams; i++) {
                indent(o, 1);
                put_word(o, "PARAM ");
                put_word(o, dl->fn->params[i].name);
                fputc(' ', o);
                dump_ty_annot(o, dl->fn->params[i].ty, dl->fn->params[i].tname);
                fputc('\n', o);
            }
            for (int i = 0; i < dl->fn->nbody; i++)
                dump_stmt(o, dl->fn->body[i], 1);
            break;
        case D_TIER:
            put_word(o, "TIER ");
            put_word(o, dl->name);
            fputc('\n', o);
            break;
        case D_USE:
            put_word(o, "USE ");
            put_word(o, dl->name);
            fputc('\n', o);
            break;
        case D_STRUCT:
            put_word(o, "STRUCT ");
            put_word(o, dl->st->name);
            fputc('\n', o);
            for (int i = 0; i < dl->st->nfields; i++) {
                indent(o, 1);
                put_word(o, "FIELD ");
                put_word(o, dl->st->fields[i].name);
                fputc(' ', o);
                dump_ty_annot(o, dl->st->fields[i].ty, dl->st->fields[i].tname);
                fputc('\n', o);
            }
            break;
        case D_ENUM:
            put_word(o, "ENUM ");
            put_word(o, dl->en->name);
            fputc('\n', o);
            for (int i = 0; i < dl->en->nvariants; i++) {
                indent(o, 1);
                put_word(o, "VARIANT ");
                put_word(o, dl->en->variants[i].name);
                fputc('\n', o);
                for (int k = 0; k < dl->en->variants[i].npayloads; k++) {
                    indent(o, 2);
                    put_word(o, "PAYLOAD ");
                    dump_ty_annot(o, dl->en->variants[i].payloads[k].ty,
                                  dl->en->variants[i].payloads[k].tname);
                    fputc('\n', o);
                }
            }
            break;
        case D_LET:
            put_word(o, dl->is_const ? "CONST " : "LET ");
            put_word(o, dl->name);
            fputc('\n', o);
            break;
        }
    }
}
