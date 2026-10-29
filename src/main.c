/* main.c - ralt driver. build | run | check | emit | explain. */
#include "common.h"
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

static void usage(void) {
    fputs(
        "ralt - the Tripon toolchain (.tp files)\n"
        "\n"
        "  ralt build <file.tp> [-o out]  [-O fast] [-fast]  build an executable\n"
        "  ralt run   <file.tp> [args...]                  build + execute\n"
        "  ralt check <file.tp> [--json]                   typecheck with diagnostics\n"
        "  ralt emit  --c file.tp -o out.c                 stop after C codegen\n"
        "  ralt explain <code>                             e.g. E0202\n"
        "  ralt init  [name]                              scaffold a .tp project (or ./name/)\n"
        "  ralt install <name|url|dir>                     resolve/install a dep\n"
        "  ralt deps                                       list collected dep files\n"
        "  ralt fmt <file.tp>                              print canonical form\n"
        "  ralt lint <file.tp> [--json]                    tier-ceiling lint\n"
        "  ralt doc <file.tp> [--json]                     fn signatures\n"
        "  ralt lsp                                        editor/agent server\n"
        "\n"
        "  -O fast   enable opt-level code paths in the C pipeline\n"
        "  -fast     integer overflow wraps instead of trapping (no-UB stays)\n",
        stderr);
}

static char *read_all(const char *path, size_t *len) {
    FILE *f = fopen(path, "rb");
    if (!f) return NULL;
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    if (n < 0) { fclose(f); return NULL; }
    char *buf = malloc((size_t)n + 1);
    if (!buf) { fclose(f); exit(1); }
    if (fread(buf, 1, (size_t)n, f) != (size_t)n) { fclose(f); free(buf); return NULL; }
    buf[n] = 0;
    fclose(f);
    *len = (size_t)n;
    return buf;
}

static void mkdir_p(const char *dir) {
    char tmp[1024];
    snprintf(tmp, sizeof tmp, "%s", dir);
    for (char *p = tmp + 1; *p; p++) {
        if (*p == '/') {
            *p = 0;
            mkdir(tmp, 0755);
            *p = '/';
        }
    }
    mkdir(tmp, 0755);
}

/* pipeline shared by build/check: parse + typecheck, one file */
static Decl **analyze(Arena *a, const char *path, int *ndecls) {
    size_t len;
    char *src = read_all(path, &len);
    if (!src) {
        fprintf(stderr, "ralt: cannot read %s\n", path);
        exit(2);
    }
    int ntoks;
    Token *toks = lex_file(a, src, len, path, &ntoks);
    Decl **decls = parse_file(a, toks, ntoks, path);
    int n = 0;
    while (decls && decls[n]) n++;
    if (g_nerrors == 0) typecheck_file(a, decls, n);
    *ndecls = n;
    return decls;
}

/* analyze + dependency merge: ralt.yaml deps fold into the same translation
 * unit (v0: typed together, externs shared). Dep order: collect() sort. */
static Decl **analyze_proj(Arena *a, const char *path, int *ndecls) {
    char **deps = NULL;
    int ndeps = 0;
    bool have_deps = deps_manifest_exists() && deps_collect(&deps, &ndeps) == 0;
    if (!have_deps || ndeps == 0) {
        if (deps) deps_free(&deps, ndeps);
        return analyze(a, path, ndecls);
    }

    int nall = 0;
    Decl ***parts = (Decl ***)malloc(((size_t)ndeps + 1) * sizeof(*parts));
    int *counts = (int *)calloc((size_t)ndeps + 1, sizeof(int));
    if (!parts || !counts) exit(1);

    for (int i = 0; i < ndeps; i++) {
        size_t len;
        char *src = read_all(deps[i], &len);
        if (!src) {
            fprintf(stderr, "ralt: cannot read dependency %s\n", deps[i]);
            exit(2);
        }
        int ntoks;
        Token *toks = lex_file(a, src, len, deps[i], &ntoks);
        parts[i] = parse_file(a, toks, ntoks, deps[i]);
        int n = 0;
        while (parts[i] && parts[i][n]) n++;
        counts[i] = n;
        nall += n;
    }
    size_t len;
    char *src = read_all(path, &len);
    if (!src) {
        fprintf(stderr, "ralt: cannot read %s\n", path);
        exit(2);
    }
    int ntoks;
    Token *toks = lex_file(a, src, len, path, &ntoks);
    parts[ndeps] = parse_file(a, toks, ntoks, path);
    int nmain = 0;
    while (parts[ndeps] && parts[ndeps][nmain]) nmain++;
    counts[ndeps] = nmain;
    nall += nmain;

    Decl **merged = (Decl **)calloc(((size_t)nall + 1), sizeof *merged);
    int k = 0;
    for (int i = ndeps; i >= 0; i--) {   /* main last: own names win prepass warns */
        for (int j = 0; j < counts[i]; j++) merged[k++] = parts[i][j];
    }
    if (g_nerrors == 0) typecheck_file(a, merged, nall);
    *ndecls = nall;
    deps_free(&deps, ndeps);
    free(parts);
    free(counts);
    return merged;
}

int main(int argc, char **argv) {
    if (argc < 2) {
        usage();
        return 2;
    }
    const char *cmd = argv[1];

    if (strcmp(cmd, "explain") == 0) {
        if (argc < 3) { usage(); return 2; }
        const char *arg = argv[2];
        if (arg[0] == 'E' || arg[0] == 'e') arg++;
        int code = atoi(arg);
        const ErrEntry *e = err_lookup(code);
        printf("E%04d\nseverity: %s\nname: %s\nhint: %s\n", code,
               e->sev == SEV_ERROR ? "error" : e->sev == SEV_WARN ? "warn" : "note",
               e->name, e->hint);
        return strcmp(e->name, "internal") == 0 && code != 0 ? 1 : 0;
    }

    /* server mode needs no file argument */
    if (strcmp(cmd, "lsp") == 0) {
        lsp_serve();
        return 0;
    }

    /* manifest commands: files not required */
    if (strcmp(cmd, "init") == 0) {
        const char *argname = argc > 2 ? argv[2] : NULL;
        int rc = deps_init_template(argname);
        if (rc == 2) { fprintf(stderr, "ralt: ralt.yaml already exists here\n"); return 2; }
        if (rc < 0) { fprintf(stderr, "ralt: init failed\n"); return 1; }
        printf("-> scaffolded %s (ralt.yaml, src/main.tp)\n", argname ? argname : "here");
        printf("-> next: ralt run src/main.tp\n");
        return 0;
    }
    if (strcmp(cmd, "install") == 0) {
        if (argc < 3) { fprintf(stderr, "ralt install: pass a dep name from ralt.yaml, a git URL, or a directory\n"); return 2; }
        if (!deps_manifest_exists() && argc < 4) {
            /* no manifest: direct URL/dir installs still land the cache */
        }
        int rc = deps_install(argc > 2 ? argv[2] : NULL);
        return rc == 0 ? 0 : 1;
    }
    if (strcmp(cmd, "deps") == 0) {
        char **paths; int n = 0;
        if (!deps_manifest_exists()) { fputs("ralt: no ralt.yaml here\n", stderr); return 2; }
        if (deps_collect(&paths, &n) != 0) return 1;
        for (int i = 0; i < n; i++) printf("%s\n", paths[i]);
        deps_free(&paths, n);
        return 0;
    }

    const char *file = NULL;
    const char *outname = NULL;
    const char *backend = "c";
    bool json = false;
    bool fast = false;
    bool ofast = false;
    bool want_emit = false;

    for (int i = 2; i < argc; i++) {
        const char *s = argv[i];
        if (s[0] != '-') { file = s; continue; }
        if (strcmp(s, "--json") == 0) json = true;
        else if (strcmp(s, "-fast") == 0) fast = true;
        else if (strcmp(s, "-O") == 0 && i + 1 < argc) { i++; ofast = strcmp(argv[i], "fast") == 0; }
        else if (strcmp(s, "-o") == 0 && i + 1 < argc) outname = argv[++i];
        else if (strcmp(s, "--c") == 0) want_emit = true;
        else if (strcmp(s, "--backend") == 0 && i + 1 < argc) backend = argv[++i];
        else { fprintf(stderr, "ralt: unknown option %s\n", s); return 2; }
    }
    (void)want_emit;
    if (!file) { usage(); return 2; }

    Arena *a = arena_new();
    if (!a) { fputs("ralt: arena init failed\n", stderr); return 2; }

    if (strcmp(cmd, "emit") == 0) {
        int ndecls;
        Decl **decls = analyze(a, file, &ndecls);
        const char *outpath = outname ? outname : "build/out.c";
        char dirbuf[1024];
        snprintf(dirbuf, sizeof dirbuf, "%s", outpath);
        char *slash = strrchr(dirbuf, '/');
        if (slash) { *slash = 0; mkdir_p(dirbuf); }
        codegen_file(a, decls, ndecls, outpath, fast);
        return 0;
    }

    if (strcmp(cmd, "check") == 0) {
        int ndecls;
        Decl **decls = analyze_proj(a, file, &ndecls);
        (void)decls; (void)ndecls;
        print_diags(json);
        return g_nerrors > 0 ? 1 : 0;
    }

    if (strcmp(cmd, "lint") == 0) {
        /* parse-only: a lib without main is a legal lint target */
        size_t len;
        char *src = read_all(file, &len);
        if (!src) {
            fprintf(stderr, "ralt: cannot read %s\n", file);
            return 1;
        }
        int ntoks;
        Token *toks = lex_file(a, src, len, file, &ntoks);
        Decl **decls = parse_file(a, toks, ntoks, file);
        int n = 0;
        while (decls && decls[n]) n++;
        lint_file(a, decls, n);
        print_diags(json);
        return g_nerrors > 0 ? 1 : 0;
    }

    if (strcmp(cmd, "fmt") == 0) {
        int ndecls;
        Decl **decls = analyze(a, file, &ndecls);
        if (g_nerrors > 0) {
            print_diags(false);
            fprintf(stderr, "ralt: %d error(s), cannot format\n", g_nerrors);
            return 1;
        }
        bool inplace = outname != NULL && strcmp(outname, "-w") == 0;
        if (inplace) {
            FILE *tmp = fopen("build/ralt_fmt_tmp.tp", "w");
            if (!tmp) { fputs("ralt: cannot write temp file\n", stderr); return 1; }
            fmt_file(a, decls, ndecls, tmp);
            fclose(tmp);
            char cmd2[1100];
            snprintf(cmd2, sizeof cmd2, "cp build/ralt_fmt_tmp.tp %s", file);
            if (system(cmd2) != 0) return 1;
            return 0;
        }
        fmt_file(a, decls, ndecls, stdout);
        return 0;
    }

    if (strcmp(cmd, "doc") == 0) {
        int ndecls;
        Decl **decls = analyze(a, file, &ndecls);
        if (g_nerrors > 0) {
            print_diags(false);
            fprintf(stderr, "ralt: %d error(s), cannot emit docs\n", g_nerrors);
            return 1;
        }
        doc_file(a, decls, ndecls, stdout, json);
        return 0;
    }

    if (strcmp(cmd, "tokens") == 0) {
        size_t len;
        char *src = read_all(file, &len);
        if (!src) {
            fprintf(stderr, "ralt: cannot read %s\n", file);
            return 1;
        }
        int ntoks;
        Token *toks = lex_file(a, src, len, file, &ntoks);
        for (int i = 0; i < ntoks; i++) {
            Token *t = &toks[i];
            printf("%s %d %d", tok_name(t->kind), t->span.line, t->span.col);
            if (t->text && (t->kind == TK_IDENT || t->kind == TK_INT ||
                            t->kind == TK_FLOAT || t->kind == TK_STR)) {
                fputc(' ', stdout);
                for (size_t k = 0; k < t->len; k++) {
                    unsigned char ch = (unsigned char)t->text[k];
                    if (ch == '\n') fputs("\\n", stdout);
                    else if (ch == '\t') fputs("\\t", stdout);
                    else if (ch == '\r') fputs("\\r", stdout);
                    else if (ch == '\\') fputs("\\\\", stdout);
                    else if (ch == '"') fputs("\\\"", stdout);
                    else if (ch >= 32 && ch < 127) fputc(ch, stdout);
                    else printf("\\x%02x", ch);
                }
            }
            fputc('\n', stdout);
        }
        return g_nerrors > 0 ? 1 : 0;
    }

    if (strcmp(cmd, "tree") == 0) {
        /* P3.1 oracle: post-parse AST, prefix + indentation, frozen format */
        size_t len;
        char *src = read_all(file, &len);
        if (!src) {
            fprintf(stderr, "ralt: cannot read %s\n", file);
            return 1;
        }
        int ntoks2;
        Token *toks2 = lex_file(a, src, len, file, &ntoks2);
        Decl **decls2 = parse_file(a, toks2, ntoks2, file);
        int n = 0;
        while (decls2 && decls2[n]) n++;
        parse_tree_dump(stdout, decls2, n);
        return g_nerrors > 0 ? 1 : 0;
    }

    if (strcmp(cmd, "build") == 0 || strcmp(cmd, "run") == 0) {
        int ndecls;
        Decl **decls = analyze_proj(a, file, &ndecls);
        if (g_nerrors > 0) {
            print_diags(false);
            fprintf(stderr, "ralt: %d error(s), build failed\n", g_nerrors);
            return 1;
        }
        mkdir_p("build");
        int status = 0, st = 0;
        const char *slash = strrchr(file, '/');
        const char *stem = slash ? slash + 1 : file;
        char cpath[1024], binpath[1024];
        {
            const char *dot = strrchr(stem, '.');
            int stemlen = dot ? (int)(dot - stem) : (int)strlen(stem);
            snprintf(cpath, sizeof cpath, "build/%.*s.c", stemlen, stem);
        }
        snprintf(binpath, sizeof binpath, "%s", outname ? outname : "build/a.out");
        if (strcmp(backend, "native") == 0) {
            /* P4: x86-64 asm backend. `as` assembles, cc only links - no C
             * compilation in this path. -no-pie: simple absolute refs. */
            char spath[1024], opath[1024];
            const char *dot = strrchr(stem, '.');
            int stemlen = dot ? (int)(dot - stem) : (int)strlen(stem);
            snprintf(spath, sizeof spath, "build/%.*s.s", stemlen, stem);
            snprintf(opath, sizeof opath, "build/%.*s.o", stemlen, stem);
            native_file(a, decls, ndecls, spath, fast);
            pid_t aspid = fork();
            if (aspid == 0) {
                execlp("as", "as", "-o", opath, spath, (char *)NULL);
                _exit(127);
            }
            waitpid(aspid, &status, 0);
            st = WIFEXITED(status) ? WEXITSTATUS(status) : 1;
            if (st != 0) {
                fprintf(stderr, "ralt: as exited %d\n", st);
                return 1;
            }
            pid_t ldpid = fork();
            if (ldpid == 0) {
                const char *cc = getenv("CC");
                if (!cc || !*cc) cc = "cc";
                execlp(cc, cc, "-no-pie", "-o", binpath, opath, "-lm", (char *)NULL);
                _exit(127);
            }
            waitpid(ldpid, &status, 0);
            st = WIFEXITED(status) ? WEXITSTATUS(status) : 1;
            if (st != 0) {
                fprintf(stderr, "ralt: native link exited %d\n", st);
                return 1;
            }
            if (strcmp(cmd, "run") == 0) {
                char **child = malloc(sizeof(char *) * (size_t)argc);
                int n = 0;
                child[n++] = (char *)binpath;
                for (int i = 3; i < argc; i++) child[n++] = argv[i];
                child[n] = NULL;
                execv(binpath, child);
                fprintf(stderr, "ralt: failed to exec %s\n", binpath);
                return 127;
            }
            printf("%s\n", binpath);
            return 0;
        }
        codegen_file(a, decls, ndecls, cpath, fast);

        /* cc stage: -O0 default (builder speed), -O fast -> -O2; -lm for pow */
        pid_t pid = fork();
        if (pid == 0) {
            const char *cc = getenv("CC");
            if (!cc || !*cc) cc = "cc";
            execlp(cc, cc, "-std=c99", ofast ? "-O2" : "-O0",
                   "-o", binpath, cpath, "-lm", (char *)NULL);
            fprintf(stderr, "ralt: failed to exec %s (is a C toolchain installed?)\n", cc);
            _exit(127);
        }
        waitpid(pid, &status, 0);
        st = WIFEXITED(status) ? WEXITSTATUS(status) : 1;
        if (st != 0) {
            fprintf(stderr, "ralt: cc pipeline exited %d\n", st);
            return 1;
        }
        if (cmd[0] == 'r') {
            char **child = malloc(sizeof(char *) * (size_t)argc);
            int n = 0;
            child[n++] = (char *)binpath;
            for (int i = 3; i < argc; i++) child[n++] = argv[i];
            child[n] = NULL;
            execv(binpath, child);
            fprintf(stderr, "ralt: failed to exec %s\n", binpath);
            return 127;
        }
        printf("%s\n", binpath);
        return 0;
    }

    usage();
    return 2;
}
