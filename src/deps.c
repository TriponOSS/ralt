/* deps.c - ralt.yaml manifest, dep cache under RALT_HOME/HOME/.ralt, git clone
 * via fork+exec, recursive .tp collection. Standalone layer: only common.h
 * (for stdio/stdlib/string types) plus POSIX dirent/stat/wait. */
#include "common.h"

#include <dirent.h>
#include <errno.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>

/* ---------------- public prototypes (driver re-declares in common.h) ---------------- */

int deps_manifest_exists(void);
int deps_init_template(const char *argname);
int deps_install(const char *target);
int deps_collect(char ***paths, int *count);
void deps_free(char ***paths, int count);

/* ---------------- manifest ---------------- */

#define DEP_MAX 64
#define DEP_NAME_MAX 128
#define DEP_VAL_MAX 512

typedef struct {
    char name[DEP_NAME_MAX];
    char value[DEP_VAL_MAX];
} DepEntry;

typedef struct {
    char name[DEP_NAME_MAX];
    char version[64];
    DepEntry deps[DEP_MAX];
    int ndeps;
    int has_deps;
} Manifest;

#define PATHBUF 1024

static void str_trim(const char *in, char *out, size_t outsz) {
    const char *s = in, *e;
    size_t n;
    while (*s == ' ' || *s == '\t' || *s == '\r') s++;
    e = s + strlen(s);
    while (e > s && (e[-1] == ' ' || e[-1] == '\t' || e[-1] == '\r' || e[-1] == '\n')) e--;
    n = (size_t)(e - s);
    if (n >= outsz) n = outsz - 1;
    memcpy(out, s, n);
    out[n] = 0;
}

/* strips a `#` comment that sits after at least one space/tab */
static void strip_line_comment(char *line) {
    char *p = line;
    while (*p) {
        if (*p == '#' && p > line && (p[-1] == ' ' || p[-1] == '\t')) {
            *p = 0;
            return;
        }
        p++;
    }
}

/* bounded strcpy without -Wformat-truncation noise; truncates deliberately */
static void put(char *dst, size_t dstsz, const char *src) {
    size_t n = strlen(src);
    if (n >= dstsz) n = dstsz - 1;
    memcpy(dst, src, n);
    dst[n] = 0;
}

/* url / local-dir discriminator; for "name" we need the dep key anyway */
static int is_url(const char *v) {
    return strncmp(v, "http://", 7) == 0 || strncmp(v, "https://", 8) == 0 ||
           strncmp(v, "git://", 6) == 0 || strncmp(v, "ssh://", 6) == 0 ||
           strncmp(v, "git@", 4) == 0;
}

static int is_path(const char *v) {
    return v[0] == '/' || strncmp(v, "./", 2) == 0 || strncmp(v, "../", 3) == 0;
}

static void default_cache_root(char *out, size_t outsz) {
    const char *home = getenv("RALT_HOME");
    if (home && home[0]) {
        snprintf(out, outsz, "%s/deps", home);
    } else {
        home = getenv("HOME");
        snprintf(out, outsz, "%s/.ralt/deps", home ? home : "/tmp");
    }
}

static int manifest_load(Manifest *m) {
    FILE *f;
    char line[1024], key[DEP_NAME_MAX], val[DEP_VAL_MAX], trim[1024];
    int lineno = 0, in_deps = 0;

    memset(m, 0, sizeof *m);
    f = fopen("ralt.yaml", "r");
    if (!f) {
        fprintf(stderr, "ralt: no ralt.yaml in current directory\n");
        return 1;
    }
    while (fgets(line, sizeof line, f)) {
        const char *colon;
        lineno++;
        strip_line_comment(line);
        if (line[0] == ' ' || line[0] == '\t') {
            /* indented entry under deps: must be 'name: value' */
            if (!in_deps) {
                fprintf(stderr, "ralt.yaml:%d: unexpected indented entry outside deps:\n", lineno);
                fclose(f);
                return 1;
            }
            str_trim(line, trim, sizeof trim);
            if (!trim[0]) continue;
            colon = strchr(trim, ':');
            if (!colon) {
                fprintf(stderr, "ralt.yaml:%d: malformed dep line (expected 'name: value')\n", lineno);
                fclose(f);
                return 1;
            }
            {
                size_t klen = (size_t)(colon - trim);
                if (klen >= sizeof key) klen = sizeof key - 1;
                memcpy(key, trim, klen);
                key[klen] = 0;
                str_trim(colon + 1, val, sizeof val);
            }
            if (!key[0] || !val[0] ||
                (!is_url(val) && !is_path(val))) {
                fprintf(stderr,
                        "ralt.yaml:%d: dep value must be an http(s)/git URL or a local path (./ or /)\n",
                        lineno);
                fclose(f);
                return 1;
            }
            if (m->ndeps == DEP_MAX) {
                fprintf(stderr, "ralt.yaml:%d: too many deps (max %d)\n", lineno, DEP_MAX);
                fclose(f);
                return 1;
            }
            put(m->deps[m->ndeps].name, DEP_NAME_MAX, key);
            put(m->deps[m->ndeps].value, DEP_VAL_MAX, val);
            m->ndeps++;
            continue;
        }

        str_trim(line, trim, sizeof trim);
        if (!trim[0]) continue;
        colon = strchr(trim, ':');
        if (!colon) {
            fprintf(stderr, "ralt.yaml:%d: malformed line (expected 'key: value')\n", lineno);
            fclose(f);
            return 1;
        }
        {
            size_t klen = (size_t)(colon - trim);
            if (klen >= sizeof key) klen = sizeof key - 1;
            memcpy(key, trim, klen);
            key[klen] = 0;
            str_trim(colon + 1, val, sizeof val);
        }

        in_deps = 0;
        if (strcmp(key, "name") == 0) {
            put(m->name, DEP_NAME_MAX, val);
        } else if (strcmp(key, "version") == 0) {
            put(m->version, sizeof m->version, val);
        } else if (strcmp(key, "deps") == 0) {
            if (val[0]) {
                fprintf(stderr, "ralt.yaml:%d: 'deps:' takes indented entries, not an inline value\n", lineno);
                fclose(f);
                return 1;
            }
            m->has_deps = 1;
            in_deps = 1;
        } else {
            fprintf(stderr, "ralt.yaml:%d: unknown key '%s' (expected name, version, deps)\n", lineno, key);
            fclose(f);
            return 1;
        }
    }
    fclose(f);
    if (m->has_deps && m->ndeps == 0)
        fprintf(stderr, "ralt: warning: ralt.yaml has empty deps:\n");
    return 0;
}

/* ---------------- fs helpers ---------------- */

static int dir_exists(const char *path) {
    struct stat st;
    return stat(path, &st) == 0 && S_ISDIR(st.st_mode);
}

/* mkdir -p equivalent; returns 0 ok */
static int mkdir_p(const char *path) {
    char buf[PATHBUF];
    char *p;
    snprintf(buf, sizeof buf, "%s", path);
    for (p = buf + 1; *p; p++) {
        if (*p == '/') {
            *p = 0;
            if (mkdir(buf, 0777) != 0 && errno != EEXIST) return 1;
            *p = '/';
        }
    }
    if (mkdir(buf, 0777) != 0 && errno != EEXIST) return 1;
    return 0;
}

static int run_git_clone(const char *url, const char *dir) {
    pid_t pid = fork();
    int st = 0;
    if (pid < 0) return 1;
    if (pid == 0) {
        execlp("git", "git", "clone", "--depth", "1", "-q", url, dir, (char *)NULL);
        _exit(127);
    }
    if (waitpid(pid, &st, 0) < 0) return 1;
    if (!WIFEXITED(st) || WEXITSTATUS(st) != 0) return 1;
    return 0;
}

/* name from URL: last path component, .git suffix stripped */
static void url_dep_name(const char *url, char *out, size_t outsz) {
    const char *base, *end;
    size_t n;
    base = url + strlen(url);
    while (base > url && base[-1] == '/') base--;
    end = base;
    while (end > url && end[-1] != '/') end--;
    base = end;
    n = strlen(base);
    if (n >= 4 && strcmp(base + n - 4, ".git") == 0) n -= 4;
    if (n >= outsz) n = outsz - 1;
    memcpy(out, base, n);
    out[n] = 0;
}

/* ---------------- public: manifest existence + init ---------------- */

int deps_manifest_exists(void) {
    struct stat st;
    return stat("ralt.yaml", &st) == 0;
}

int deps_init_template(const char *argname) {
    char cwd[PATHBUF];
    char name[DEP_NAME_MAX];
    const char *base;
    struct stat st;
    FILE *f;

    if (argname && argname[0]) {
        /* project name or path: scaffold into ./<argname>/ (created) */
        const char *base2 = argname + strlen(argname);
        while (base2 > argname && base2[-1] != '/' && base2[-1] != '\\') base2--;
        size_t blen = strlen(base2);
        if (blen == 0 || blen >= DEP_NAME_MAX || strlen(argname) >= 128) {
            fprintf(stderr, "ralt: init: bad project name\n");
            return -1;
        }
        if (mkdir_p(argname) != 0) {
            fprintf(stderr, "ralt: init: cannot create %s: %s\n", argname,
                    strerror(errno));
            return -1;
        }
        if (chdir(argname) != 0) {
            fprintf(stderr, "ralt: init: cannot enter %s: %s\n", argname,
                    strerror(errno));
            return -1;
        }
        if (deps_manifest_exists()) {
            fprintf(stderr, "ralt: ralt.yaml already exists in %s\n", argname);
            return 2;
        }
        snprintf(name, sizeof name, "%s", base2);
    } else {
        if (deps_manifest_exists()) {
            fprintf(stderr, "ralt: ralt.yaml already exists here\n");
            return 2;
        }
        if (!getcwd(cwd, sizeof cwd)) {
            fprintf(stderr, "ralt: cannot determine current directory\n");
            return -1;
        }
        base = cwd + strlen(cwd);
        while (base > cwd && base[-1] != '/' && base[-1] != '\\') base--;
        if (base[0] == 0 || strlen(base) >= DEP_NAME_MAX)
            snprintf(name, sizeof name, "tripon-app");
        else
            snprintf(name, sizeof name, "%s", base);
    }

    if (mkdir("src", 0777) != 0 && errno != EEXIST) {
        fprintf(stderr, "ralt: init: cannot create src/: %s\n", strerror(errno));
            return -1;
    }
    if (stat("src/main.tp", &st) == 0) {
        fprintf(stderr, "ralt: src/main.tp already exists, keeping it\n");
    } else {
        f = fopen("src/main.tp", "w");
        if (!f) {
            fprintf(stderr, "ralt: init: cannot write src/main.tp: %s\n",
                    strerror(errno));
            return -1;
        }
        fprintf(f,
                "use tier core;\n"
                "\n"
                "// %s - a Tripon program (.tp)\n"
                "fn main() -> i32 {\n"
                "    print_str(\"hello, tripon\");\n"
                "    return 0;\n"
                "}\n",
                name);
        fclose(f);
    }

    f = fopen("ralt.yaml", "w");
    if (!f) {
        fprintf(stderr, "ralt: cannot write ralt.yaml: %s\n", strerror(errno));
        return -1;
    }
    fprintf(f,
            "name: %s\n"
            "version: 0.1.0\n"
            "deps:\n",
            name);
    fclose(f);

    if (stat(".gitignore", &st) != 0) {
        f = fopen(".gitignore", "w");
        if (f) {
            fputs("build/\n*.out\n", f);
            fclose(f);
        }
    }
    return 1;
}

/* ---------------- public: install ---------------- */

int deps_install(const char *target) {
    char root[PATHBUF], dir[PATHBUF], depname[DEP_NAME_MAX], value[DEP_VAL_MAX];
    Manifest m;
    int found = 0;

    if (!target || !target[0]) {
        fprintf(stderr, "ralt: install: empty target\n");
        return 1;
    }
    /* resolve via manifest when target is a dep name */
    if (manifest_load(&m) == 0) {
        for (int i = 0; i < m.ndeps; i++) {
            if (strcmp(m.deps[i].name, target) == 0) {
                found = 1;
                put(depname, sizeof depname, m.deps[i].name);
                put(value, sizeof value, m.deps[i].value);
                break;
            }
        }
    }
    if (!found) {
        /* target is a raw URL or local dir path, used directly */
        put(value, sizeof value, target);
        if (is_url(value)) {
            url_dep_name(value, depname, sizeof depname);
        } else {
            put(depname, sizeof depname, target);
        }
    }

    if (is_url(value)) {
        default_cache_root(root, sizeof root);
        if (mkdir_p(root) != 0) {
            fprintf(stderr, "ralt: cannot create cache dir %s\n", root);
            return 1;
        }
        snprintf(dir, sizeof dir, "%.*s/%.*s", (int)(sizeof dir - DEP_NAME_MAX - 1), root, DEP_NAME_MAX - 1, depname);
        if (dir_exists(dir)) {
            printf("-> %s cached (%s)\n", depname, dir);
            return 0;
        }
        printf("-> %s cloning %s\n", depname, value);
        if (run_git_clone(value, dir) != 0) {
            fprintf(stderr, "ralt: git clone failed for %s into %s\n", value, dir);
            return 1;
        }
        printf("-> %s cloned\n", depname);
        return 0;
    }

    /* local dir: used as-is, no copy */
    if (!dir_exists(value)) {
        fprintf(stderr, "ralt: local dep %s: no such directory: %s\n", depname, value);
        return 1;
    }
    printf("-> %s local (%s)\n", depname, value);
    return 0;
}

/* ---------------- public: collect ---------------- */

typedef struct {
    char **items;
    int len, cap;
} StrList;

static void strlist_push(StrList *l, const char *s) {
    if (l->len == l->cap) {
        l->cap = l->cap ? l->cap * 2 : 16;
        l->items = realloc(l->items, (size_t)l->cap * sizeof(char *));
        if (!l->items) { fputs("ralt: out of memory\n", stderr); exit(1); }
    }
    size_t n = strlen(s);
    l->items[l->len] = malloc(n + 1);
    if (!l->items[l->len]) { fputs("ralt: out of memory\n", stderr); exit(1); }
    memcpy(l->items[l->len], s, n + 1);
    l->len++;
}

static int name_in(const char *name, const char *a, const char *b, const char *c,
                   const char *d) {
    return strcmp(name, a) == 0 || strcmp(name, b) == 0 ||
           strcmp(name, c) == 0 || (d && strcmp(name, d) == 0);
}

static void walk_collect(const char *dir, StrList *out) {
    DIR *d = opendir(dir);
    struct dirent *ent;
    char sub[PATHBUF];
    struct stat st;

    if (!d) {
        fprintf(stderr, "ralt: cannot open dependency directory %s\n", dir);
        return;
    }
    while ((ent = readdir(d)) != NULL) {
        if (strcmp(ent->d_name, ".") == 0 || strcmp(ent->d_name, "..") == 0) continue;
        snprintf(sub, sizeof sub, "%s/%s", dir, ent->d_name);
        if (stat(sub, &st) != 0) continue;
        if (S_ISDIR(st.st_mode)) {
            /* selfhost sources are self-contained units: never folded into
             * foreign dep translation units, they carry their own mains */
            if (name_in(ent->d_name, "tests", "examples", "bench", "selfhost")) continue;
            walk_collect(sub, out);
        } else if (S_ISREG(st.st_mode)) {
            size_t n = strlen(ent->d_name);
            if (n >= 3 && strcmp(ent->d_name + n - 3, ".tp") == 0)
                strlist_push(out, sub);
        }
    }
    closedir(d);
}

static int cmp_strptr(const void *a, const void *b) {
    const char *const *pa = a, *const *pb = b;
    return strcmp(*pa, *pb);
}

static int refresh_one_dep(const DepEntry *dep) {
    if (is_url(dep->value)) return deps_install(dep->name);
    if (!dir_exists(dep->value)) {
        fprintf(stderr, "ralt: dep %s: no such directory: %s\n", dep->name, dep->value);
        return 1;
    }
    return 0;
}

int deps_collect(char ***paths, int *count) {
    Manifest m;
    StrList list = {NULL, 0, 0};

    *paths = NULL;
    *count = 0;
    char root[PATHBUF];

    if (manifest_load(&m) != 0) return 1;
    if (!m.has_deps) return 0;   /* no deps key: nothing to do */

    default_cache_root(root, sizeof root);
    for (int i = 0; i < m.ndeps; i++) {
        char src[PATHBUF];
        if (refresh_one_dep(&m.deps[i]) != 0) {
            while (list.len) free(list.items[--list.len]);
            free(list.items);
            return 1;
        }
        if (is_url(m.deps[i].value)) {
            snprintf(src, sizeof src, "%.*s/%.*s", (int)(sizeof src - DEP_NAME_MAX - 1), root, DEP_NAME_MAX - 1, m.deps[i].name);
        } else {
            put(src, sizeof src, m.deps[i].value);
        }
        if (!dir_exists(src)) {
            fprintf(stderr, "ralt: dep %s: directory missing after install: %s\n",
                    m.deps[i].name, src);
            while (list.len) free(list.items[--list.len]);
            free(list.items);
            return 1;
        }
        walk_collect(src, &list);
    }
    qsort(list.items, (size_t)list.len, sizeof(char *), cmp_strptr);

    if (list.len == 0) {
        free(list.items);
        return 0;
    }
    *paths = malloc((size_t)list.len * sizeof(char *));
    if (!*paths) { fputs("ralt: out of memory\n", stderr); exit(1); }
    memcpy(*paths, list.items, (size_t)list.len * sizeof(char *));
    *count = list.len;
    free(list.items);
    return 0;
}

void deps_free(char ***paths, int count) {
    if (!paths || !*paths) {
        *paths = NULL;
        return;
    }
    for (int i = 0; i < count; i++)
        free((*paths)[i]);
    free(*paths);
    *paths = NULL;
}
