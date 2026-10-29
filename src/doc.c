/* doc.c - `ralt doc`: signatures + leading doc comments. text or json. */
#include "common.h"
#include <ctype.h>

void doc_file(Arena *a, Decl **decls, int ndecls, FILE *out, bool json) {
    if (json) {
        fputs("[\n", out);
    }
    int nd = 0;
    for (int i = 0; i < ndecls; i++) {
        if (decls[i]->kind != D_FN) continue;
        FnDecl *fn = decls[i]->fn;
        char sig[1024];
        int n = snprintf(sig, sizeof sig, "fn %s(", fn->name);
        for (int k = 0; k < fn->nparams; k++) {
            n += snprintf(sig + n, sizeof sig - (size_t)n, "%s%s: %s",
                          k ? ", " : "", fn->params[k].name, ty_name(fn->params[k].ty));
        }
        n += snprintf(sig + n, sizeof sig - (size_t)n, ")");
        if (fn->ret != TY_VOID)
            n += snprintf(sig + n, sizeof sig - (size_t)n, " -> %s", ty_name(fn->ret));

        if (json) {
            if (nd) fputs(",\n", out);
            fprintf(out, "  { \"symbol\": ");
            /* reuse print helper: minimal inline quoting */
            fputc('"', out);
            for (const char *p = fn->name; *p; p++) fputc(*p, out);
            fprintf(out, "\", \"signature\": ");
            fputc('"', out);
            for (const char *p = sig; *p; p++) {
                if (*p == '"') fputs("\\\"", out);
                else fputc(*p, out);
            }
            fprintf(out, "\", \"file\": \"%s\", \"line\": %d }",
                    fn->span.file, fn->span.line);
        } else {
            fprintf(out, "%s\n", sig);
        }
        nd++;
    }
    if (json) {
        fputs("\n]\n", out);
    }
    (void)a;
}
