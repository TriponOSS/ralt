/* module.c - phase-1 file modules.
 *
 *   use "lib/math.tp" as math;
 *   let r = math::add(1, 2);
 *
 * A module is parsed and folded into the same translation unit like a dep.
 * Every function in it is renamed to <alias>__<name> (so modules cannot
 * collide), internal calls are rewritten to the mangled names, and only
 * `pub fn` names are registered as reachable through the alias. Types are
 * not namespaced yet.
 */
#include "common.h"
#include <sys/stat.h>

#define MOD_MAX 64
#define MOD_NAME 160

typedef struct { char alias[MOD_NAME]; } AliasEnt;
typedef struct { char alias[MOD_NAME]; char name[MOD_NAME]; } PubEnt;

static AliasEnt g_aliases[MOD_MAX];
static int g_nalias;
static PubEnt g_pubs[MOD_MAX * 8];
static int g_npubs;

void module_reset(void) {
    g_nalias = 0;
    g_npubs = 0;
}

void module_alias_add(const char *alias) {
    if (!alias || module_alias_has(alias)) return;
    if (g_nalias >= MOD_MAX) return;
    snprintf(g_aliases[g_nalias].alias, MOD_NAME, "%s", alias);
    g_nalias++;
}

bool module_alias_has(const char *alias) {
    if (!alias) return false;
    for (int i = 0; i < g_nalias; i++)
        if (strcmp(g_aliases[i].alias, alias) == 0) return true;
    return false;
}

void module_pub_add(const char *alias, const char *name) {
    if (g_npubs >= MOD_MAX * 8) return;
    snprintf(g_pubs[g_npubs].alias, MOD_NAME, "%s", alias);
    snprintf(g_pubs[g_npubs].name, MOD_NAME, "%s", name);
    g_npubs++;
}

bool module_pub_has(const char *alias, const char *name) {
    for (int i = 0; i < g_npubs; i++)
        if (strcmp(g_pubs[i].alias, alias) == 0 &&
            strcmp(g_pubs[i].name, name) == 0) return true;
    return false;
}

/* ---------------- helpers ---------------- */

static char *slurp(const char *path, size_t *len) {
    FILE *f = fopen(path, "rb");
    if (!f) return NULL;
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    if (n < 0) { fclose(f); return NULL; }
    char *buf = malloc((size_t)n + 1);
    if (!buf) { fclose(f); return NULL; }
    size_t got = fread(buf, 1, (size_t)n, f);
    fclose(f);
    buf[got] = 0;
    *len = got;
    return buf;
}

static bool file_exists(const char *p) {
    struct stat st;
    return stat(p, &st) == 0 && S_ISREG(st.st_mode);
}

static void resolve_path(const char *path, const char *base_dir,
                         char *out, size_t outsz) {
    if (path[0] == '/' || !base_dir || !base_dir[0]) {
        snprintf(out, outsz, "%s", path);
        return;
    }
    snprintf(out, outsz, "%s/%s", base_dir, path);
    if (file_exists(out)) return;
    snprintf(out, outsz, "%s", path);   /* fall back to cwd-relative */
}

static bool name_in(const char *nm, char **names, int n) {
    if (!nm) return false;
    for (int i = 0; i < n; i++)
        if (names[i] && strcmp(nm, names[i]) == 0) return true;
    return false;
}

static const char *mangle(Arena *a, const char *alias, const char *name) {
    char buf[2 * MOD_NAME + 3];
    snprintf(buf, sizeof buf, "%s__%s", alias, name);
    return arena_dupstr(a, buf, strlen(buf));
}

/* ---------------- rewriting ---------------- */

static void rw_expr(Arena *a, Expr *e, const char *alias, char **names, int n);

static void rw_stmts(Arena *a, Stmt **ss, int ns, const char *alias,
                     char **names, int n) {
    for (int i = 0; i < ns; i++) {
        Stmt *s = ss[i];
        if (!s) continue;
        switch (s->kind) {
        case ST_LET:
            rw_expr(a, s->init, alias, names, n);
            break;
        case ST_ASSIGN:
            rw_expr(a, s->target, alias, names, n);
            rw_expr(a, s->value, alias, names, n);
            break;
        case ST_RETURN:
            rw_expr(a, s->value, alias, names, n);
            break;
        case ST_IF:
            rw_expr(a, s->cond, alias, names, n);
            rw_stmts(a, s->body, s->nbody, alias, names, n);
            if (s->els) rw_stmts(a, &s->els, 1, alias, names, n);
            break;
        case ST_WHILE:
            rw_expr(a, s->cond, alias, names, n);
            rw_stmts(a, s->body, s->nbody, alias, names, n);
            break;
        case ST_MATCH:
            rw_expr(a, s->cond, alias, names, n);
            for (int k = 0; k < s->narms; k++)
                if (s->arms[k])
                    rw_stmts(a, s->arms[k]->body, s->arms[k]->nbody,
                             alias, names, n);
            break;
        case ST_EXPR:
            rw_expr(a, s->value, alias, names, n);
            break;
        case ST_BLOCK:
            rw_stmts(a, s->body, s->nbody, alias, names, n);
            break;
        }
    }
}

static void rw_expr(Arena *a, Expr *e, const char *alias, char **names, int n) {
    if (!e) return;
    if (e->kind == EX_CALL && name_in(e->callee, names, n))
        e->callee = mangle(a, alias, e->callee);
    if (e->kind == EX_IDENT && name_in(e->sval, names, n) && e->ty == TY_FN)
        e->sval = mangle(a, alias, e->sval);
    rw_expr(a, e->lhs, alias, names, n);
    rw_expr(a, e->rhs, alias, names, n);
    rw_expr(a, e->operand, alias, names, n);
    rw_expr(a, e->base, alias, names, n);
    rw_expr(a, e->index, alias, names, n);
    for (int i = 0; i < e->nargs; i++) rw_expr(a, e->args[i], alias, names, n);
}

/* ---------------- entry ---------------- */

Decl **module_expand(Arena *a, const char *path, const char *alias,
                     const char *base_dir, Span sp, int *nout) {
    *nout = 0;
    if (!alias || !alias[0]) return NULL;
    if (module_alias_has(alias)) {
        diag(sp, E0704, SEV_ERROR, "duplicate module alias",
             "two imports share this alias; rename one");
        return NULL;
    }
    char full[1024];
    resolve_path(path, base_dir, full, sizeof full);
    size_t len = 0;
    char *src = slurp(full, &len);
    if (!src) {
        char msg[320];
        snprintf(msg, sizeof msg, "cannot read module '%s'", path);
        diag(sp, E0703, SEV_ERROR, msg, "check the path in the use statement");
        return NULL;
    }
    int ntoks = 0;
    Token *toks = lex_file(a, src, len, full, &ntoks);
    Decl **decls = parse_file(a, toks, ntoks, full);
    free(src);

    int n = 0;
    while (decls && decls[n]) n++;

    /* collect original fn names before mangling */
    char **names = malloc(sizeof(char *) * (size_t)(n ? n : 1));
    int nn = 0;
    for (int i = 0; i < n; i++)
        if (decls[i]->kind == D_FN && decls[i]->fn)
            names[nn++] = (char *)decls[i]->fn->name;

    /* export registration + rename */
    for (int i = 0; i < n; i++) {
        Decl *d = decls[i];
        if (d->kind == D_FN && d->fn) {
            if (d->is_pub) module_pub_add(alias, d->fn->name);
            d->fn->name = mangle(a, alias, d->fn->name);
        }
    }
    /* rewrite internal references to the mangled names */
    for (int i = 0; i < n; i++) {
        Decl *d = decls[i];
        if (d->kind == D_FN && d->fn)
            rw_stmts(a, d->fn->body, d->fn->nbody, alias, names, nn);
        else if (d->kind == D_LET)
            rw_expr(a, d->init, alias, names, nn);
    }
    free(names);

    module_alias_add(alias);
    *nout = n;
    return decls;
}
