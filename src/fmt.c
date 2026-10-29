/* fmt.c - `ralt fmt`: parse, re-print canonical layout.
 * Agent rule: fmt output is stable and idempotent. */
#include "common.h"

typedef struct {
    FILE *out;
    int indent;
} Fm;

static int prec_of(TokKind k) {
    switch (k) {
    case TK_OR: return 1;
    case TK_AND: return 2;
    case TK_EQ: case TK_NE: return 3;
    case TK_LT: case TK_GT: case TK_LE: case TK_GE: return 4;
    case TK_PLUS: case TK_MINUS: return 5;
    case TK_STAR: case TK_SLASH: case TK_PERCENT: return 6;
    case TK_POW: return 7;
    default: return 0;
    }
}

static const char *op_word(TokKind k) {
    switch (k) {
    case TK_OR: return "||";
    case TK_AND: return "&&";
    case TK_EQ: return "==";
    case TK_NE: return "!=";
    case TK_LT: return "<";
    case TK_GT: return ">";
    case TK_LE: return "<=";
    case TK_GE: return ">=";
    case TK_PLUS: return "+";
    case TK_MINUS: return "-";
    case TK_STAR: return "*";
    case TK_SLASH: return "/";
    case TK_PERCENT: return "%";
    case TK_POW: return "**";
    default: return "?";
    }
}

static void fm_indent(Fm *f) {
    for (int i = 0; i < f->indent * 2; i++) fputc(' ', f->out);
}

/* composite type name: struct/enum types print their own name */
static void fm_tyname(Fm *f, Ty t, const char *tname) {
    if (t == TY_ARRAY) {
        ArrayInfo *ai = array_find(tname);
        if (!ai) { fputs(tname ? tname : ty_name(t), f->out); return; }
        fprintf(f->out, "[%d]", ai->len);
        fm_tyname(f, ai->elem_ty, ai->elem_tname);
        return;
    }
    if (t == TY_OPT || t == TY_RESULT) {
        /* rebuild the canonical opt<T> / result<T, E> from the anon shape */
        EnDecl *en = tname ? anon_find(tname) : NULL;
        if (!en) { fputs(tname ? tname : ty_name(t), f->out); return; }
        bool is_res = en->variants[1].npayloads == 1;
        fputs(is_res ? "result<" : "opt<", f->out);
        fm_tyname(f, en->variants[0].payloads[0].ty, en->variants[0].payloads[0].tname);
        if (is_res) {
            fputs(", ", f->out);
            fm_tyname(f, en->variants[1].payloads[0].ty, en->variants[1].payloads[0].tname);
        }
        fputc('>', f->out);
        return;
    }
    if ((t == TY_STRUCT || t == TY_ENUM || t == TY_TYPEDEF) && tname) fputs(tname, f->out);
    else fputs(ty_name(t), f->out);
}

static void fm_expr(Fm *f, Expr *e, int parent_prec) {
    switch (e->kind) {
    case EX_INT:
        fprintf(f->out, "%lld%s", (long long)e->ival, e->ty == TY_I64 ? "" : "");
        break;
    case EX_FLOAT:
        fprintf(f->out, "%.17g", e->fval);
        break;
    case EX_STR: {
        fputc('"', f->out);
        for (size_t i = 0; i < e->slen; i++) {
            unsigned char c = (unsigned char)e->sval[i];
            switch (c) {
            case '\n': fputs("\\n", f->out); break;
            case '\t': fputs("\\t", f->out); break;
            case '\r': fputs("\\r", f->out); break;
            case '\0': fputs("\\0", f->out); break;
            case '"':  fputs("\\\"", f->out); break;
            case '\\': fputs("\\\\", f->out); break;
            default: fputc(c, f->out);
            }
        }
        fputc('"', f->out);
        break;
    }
    case EX_BOOL:
        fputs(e->bval ? "true" : "false", f->out);
        break;
    case EX_IDENT:
        fputs(e->sval, f->out);
        break;
    case EX_FIELD:
        fm_expr(f, e->base, 100);
        fputc('.', f->out);
        fputs(e->sval, f->out);
        break;
    case EX_INDEX:
        fm_expr(f, e->base, 100);
        fputc('[', f->out);
        fm_expr(f, e->index, 0);
        fputc(']', f->out);
        break;
    case EX_STRUCTINIT: {
        fputs(e->sval, f->out);
        fputs(" { ", f->out);
        for (int i = 0; i < e->nargs; i++) {
            if (i) fputs(", ", f->out);
            fputs(e->inames[i], f->out);
            fputs(": ", f->out);
            fm_expr(f, e->args[i], 0);
        }
        fputs(" }", f->out);
        break;
    }
    case EX_VARIANT:
        if (!e->bare_ctor) {
            fputs(e->sval, f->out);
            fputs("::", f->out);
        }
        fputs(e->vname, f->out);
        if (e->nargs > 0) {
            fputc('(', f->out);
            for (int i = 0; i < e->nargs; i++) {
                if (i) fputs(", ", f->out);
                fm_expr(f, e->args[i], 0);
            }
            fputc(')', f->out);
        }
        break;
    case EX_SPREAD:
        fm_expr(f, e->operand, 100);
        fputc('?', f->out);
        break;
    case EX_CAST:
        fputs("cast<", f->out);
        fm_tyname(f, e->ty, e->sval);
        fputc('>', f->out);
        fputc('(', f->out);
        fm_expr(f, e->operand, 0);
        fputc(')', f->out);
        break;
    case EX_CALL:
        fputs(e->callee, f->out);
        fputc('(', f->out);
        for (int i = 0; i < e->nargs; i++) {
            if (i) fputs(", ", f->out);
            fm_expr(f, e->args[i], 0);
        }
        fputc(')', f->out);
        break;
    case EX_UN:
        if (e->unop == UN_NOT) fputc('!', f->out);
        else fputc('-', f->out);
        fm_expr(f, e->operand, 100);
        break;
    case EX_BIN: {
        int my = prec_of(e->op);
        bool wrap = my < parent_prec;
        if (wrap) fputc('(', f->out);
        fm_expr(f, e->lhs, my);
        fprintf(f->out, " %s ", op_word(e->op));
        fm_expr(f, e->rhs, my + 1);
        if (wrap) fputc(')', f->out);
        break;
    }
    default: break;
    }
}

static void fm_stmts(Fm *f, Stmt **body, int nbody);

static void fm_if(Fm *f, Stmt *s) {   /* prints the whole if/else-if/else chain inline */
    fputs("if ", f->out);
    fm_expr(f, s->cond, 0);
    fputs(" {\n", f->out);
    f->indent++;
    fm_stmts(f, s->body, s->nbody);
    f->indent--;
    fm_indent(f);
    fputs("}", f->out);
    if (s->els) {
        if (s->els->kind == ST_IF) {
            fputs(" else ", f->out);
            fm_if(f, s->els);
        } else {
            fputs(" else {\n", f->out);
            f->indent++;
            fm_stmts(f, s->els->body, s->els->nbody);
            f->indent--;
            fm_indent(f);
            fputs("}", f->out);
        }
    }
}

static void fm_stmt(Fm *f, Stmt *s) {
    switch (s->kind) {
    case ST_LET:
        fm_indent(f);
        fputs(s->is_const ? "const " : "let ", f->out);
        fputs(s->name, f->out);
        if (s->ty != TY_UNSET) {
            fputs(": ", f->out);
            fm_tyname(f, s->ty, s->tname);
        }
        if (s->init) {
            fputs(" = ", f->out);
            fm_expr(f, s->init, 0);
        }
        fputs(";\n", f->out);
        break;
    case ST_ASSIGN:
        fm_indent(f);
        fm_expr(f, s->target, 0);
        fprintf(f->out, " %s ", op_word(s->aop) ? (s->aop == TK_ASSIGN ? "=" :
                s->aop == TK_ADDEQ ? "+=" : s->aop == TK_SUBEQ ? "-=" :
                s->aop == TK_MULEQ ? "*=" : s->aop == TK_DIVEQ ? "/=" : "%=") : "=");
        fm_expr(f, s->value, 0);
        fputs(";\n", f->out);
        break;
    case ST_RETURN:
        fm_indent(f);
        fputs("return", f->out);
        if (s->value) {
            fputc(' ', f->out);
            fm_expr(f, s->value, 0);
        }
        fputs(";\n", f->out);
        break;
    case ST_IF:
        fm_indent(f);
        fm_if(f, s);
        fputs("\n", f->out);
        break;
    case ST_WHILE:
        fm_indent(f);
        fputs("while ", f->out);
        fm_expr(f, s->cond, 0);
        fputs(" {\n", f->out);
        f->indent++;
        fm_stmts(f, s->body, s->nbody);
        f->indent--;
        fm_indent(f);
        fputs("}\n", f->out);
        break;
    case ST_MATCH: {  /* arm pattern line; arm bodies always blocks */
        fm_indent(f);
        fputs("match ", f->out);
        fm_expr(f, s->cond, 0);
        fputs(" {\n", f->out);
        f->indent++;
        for (int i = 0; i < s->narms; i++) {
            MatchArm *arm = s->arms[i];
            fm_indent(f);
            switch (arm->pkind) {
            case PAT_WILD: fputs("_", f->out); break;
            case PAT_LIT_INT: fprintf(f->out, "%lld", (long long)arm->ival); break;
            case PAT_LIT_BOOL: fputs(arm->bval ? "true" : "false", f->out); break;
            case PAT_VARIANT:
                if (arm->ename) { fputs(arm->ename, f->out); fputs("::", f->out); }
                fputs(arm->vname, f->out);
                if (arm->nbinds > 0) {
                    fputc('(', f->out);
                    for (int k = 0; k < arm->nbinds; k++) {
                        if (k) fputs(", ", f->out);
                        fputs(arm->binds[k], f->out);
                    }
                    fputc(')', f->out);
                }
                break;
            }
            if (arm->nbody == 0) {
                fputs(" => {}\n", f->out);
            } else {
                fputs(" => {\n", f->out);
                f->indent++;
                fm_stmts(f, arm->body, arm->nbody);
                f->indent--;
                fm_indent(f);
                fputs("}\n", f->out);
            }
        }
        f->indent--;
        fm_indent(f);
        fputs("}\n", f->out);
        break;
    }
    case ST_EXPR:
        fm_indent(f);
        fm_expr(f, s->value, 0);
        fputs(";\n", f->out);
        break;
    case ST_BLOCK:
        fm_indent(f);
        fputs("{\n", f->out);
        f->indent++;
        fm_stmts(f, s->body, s->nbody);
        f->indent--;
        fm_indent(f);
        fputs("}\n", f->out);
        break;
    default: break;
    }
}

static void fm_stmts(Fm *f, Stmt **body, int nbody) {
    for (int i = 0; i < nbody; i++) fm_stmt(f, body[i]);
}

void fmt_file(Arena *a, Decl **decls, int ndecls, FILE *out) {
    Fm f;
    f.out = out;
    f.indent = 0;
    for (int i = 0; i < ndecls; i++) {
        Decl *d = decls[i];
        if (d->kind == D_TIER) {
            fprintf(out, "use tier %s;\n", d->name);
        } else if (d->kind == D_FN) {
            FnDecl *fn = d->fn;
            bool fn_extern = fn->is_extern;
            if (fn_extern) {
                fprintf(out, "extern \"C\" {\n");
                fprintf(out, "    fn %s(", fn->name);
                for (int k = 0; k < fn->nparams; k++) {
                    if (k) fputs(", ", out);
                    fprintf(out, "%s: ", fn->params[k].name);
                    fm_tyname(&f, fn->params[k].ty, fn->params[k].tname);
                }
                fprintf(out, ")");
                if (fn->ret != TY_VOID) {
                    fprintf(out, " -> ");
                    fm_tyname(&f, fn->ret, fn->retname);
                }
                fprintf(out, ";\n}\n");
            } else {
                fprintf(out, "fn %s(", fn->name);
                for (int k = 0; k < fn->nparams; k++) {
                    if (k) fputs(", ", out);
                    fprintf(out, "%s: ", fn->params[k].name);
                    fm_tyname(&f, fn->params[k].ty, fn->params[k].tname);
                }
                fprintf(out, ")");
                if (fn->ret != TY_VOID) {
                    fprintf(out, " -> ");
                    fm_tyname(&f, fn->ret, fn->retname);
                }
                fputs(" {\n", out);
                f.indent = 1;
                fm_stmts(&f, fn->body, fn->nbody);
                fputs("}\n", out);
            }
        } else if (d->kind == D_STRUCT) {
            StDecl *st = d->st;
            fprintf(out, "struct %s {\n", st->name);
            for (int k = 0; k < st->nfields; k++) {
                fprintf(out, "    %s: ", st->fields[k].name);
                fm_tyname(&f, st->fields[k].ty, st->fields[k].tname);
                fputs(";\n", out);
            }
            fputs("}\n", out);
        } else if (d->kind == D_ENUM) {
            EnDecl *en = d->en;
            fprintf(out, "enum %s {\n", en->name);
            for (int k = 0; k < en->nvariants; k++) {
                Variant *v = &en->variants[k];
                fputs("    ", out);
                fputs(v->name, out);
                if (v->npayloads > 0) {
                    fputc('(', out);
                    for (int p = 0; p < v->npayloads; p++) {
                        if (p) fputs(", ", out);
                        fm_tyname(&f, v->payloads[p].ty, v->payloads[p].tname);
                    }
                    fputc(')', out);
                }
                if (k + 1 < en->nvariants || k > 0) fputc(',', out);
                fputc('\n', out);
            }
            fputs("}\n", out);
        } else {
            fputs("\n", out);
        }
        (void)a;
        fputs("\n", out);
    }
}
