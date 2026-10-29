/* util.c - arena bump allocator + growable pointer vec */
#include "common.h"

static Arena *arena_extend(Arena *cur, size_t n) {
    Arena *a = calloc(1, sizeof *a);
    if (!a) { fputs("ralt: out of memory\n", stderr); exit(1); }
    a->cap = n > (1u << 20) ? n : (1u << 20);
    a->base = malloc(a->cap);
    if (!a->base) { fputs("ralt: out of memory\n", stderr); exit(1); }
    a->next = cur;
    return a;
}

Arena *arena_new(void) { return arena_extend(NULL, 0); }

void *arena_alloc(Arena *a, size_t n) {
    n = (n + 15) & ~(size_t)15;
    if (a->used + n > a->cap) {
        Arena *fresh = arena_extend(NULL, n);
        /* splice: caller keeps head; we thread fresh behind cur so data lands in it */
        fresh->next = a->next;
        a->next = fresh;
        a = fresh;
    }
    void *p = a->base + a->used;
    a->used += n;
    return p;
}

void *arena_zalloc(Arena *a, size_t n) {
    void *p = arena_alloc(a, n);
    memset(p, 0, n);
    return p;
}

char *arena_dupstr(Arena *a, const char *s, size_t len) {
    char *p = arena_alloc(a, len + 1);
    memcpy(p, s, len);
    p[len] = 0;
    return p;
}

void vec_push_ptr(VecPtr *v, void *p) {
    if (v->len == v->cap) {
        v->cap = v->cap ? v->cap * 2 : 8;
        v->data = realloc(v->data, (size_t)v->cap * sizeof(void *));
        if (!v->data) { fputs("ralt: out of memory\n", stderr); exit(1); }
    }
    v->data[v->len++] = p;
}

/* ---------------- types ---------------- */

static const char *TY_NAMES[] = {
    "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64",
    "isize", "usize", "f32", "f64", "bool", "str", "()",
    "struct", "enum", "typedef", "?", "opt", "result", "array", "*i8", "fn",
};
static const char *TY_CNAMES[] = {
    "int8_t", "int16_t", "int32_t", "int64_t",
    "uint8_t", "uint16_t", "uint32_t", "uint64_t",
    "intptr_t", "uintptr_t", "float", "double", "bool", "const char *", "void",
    "?struct", "?enum", "?typedef", "int32_t", "?opt", "?result", "?array",
    "char *", "void *",
};
const char *ty_name(Ty t) { return TY_NAMES[t]; }
const char *ty_cname(Ty t) { return TY_CNAMES[t]; }
bool ty_is_int(Ty t)   { return t >= TY_I8 && t <= TY_USIZE; }
bool ty_is_float(Ty t) { return t == TY_F32 || t == TY_F64; }
bool ty_is_num(Ty t)   { return ty_is_int(t) || ty_is_float(t); }

/* ---------------- fixed array registry ---------------- */

#define ARRAY_MAX 256
static ArrayInfo g_arrays[ARRAY_MAX];
static int g_narrays = 0;

ArrayInfo *array_find(const char *name) {
    if (!name) return NULL;
    for (int i = 0; i < g_narrays; i++)
        if (strcmp(g_arrays[i].name, name) == 0) return &g_arrays[i];
    return NULL;
}

ArrayInfo *array_at(int i) { return i >= 0 && i < g_narrays ? &g_arrays[i] : NULL; }
int array_count(void) { return g_narrays; }

ArrayInfo *array_declare(const char *name, int len, Ty elem, const char *elem_tname, Span sp) {
    ArrayInfo *ex = array_find(name);
    if (ex) return ex;
    if (g_narrays == ARRAY_MAX) {
        diag(sp, E0202, SEV_ERROR, "too many distinct array types in this unit",
             "v0 caps array shapes; reuse the same [N]T type");
        return NULL;
    }
    ArrayInfo *ai = &g_arrays[g_narrays++];
    ai->name = name;
    ai->len = len;
    ai->elem_ty = elem;
    ai->elem_tname = elem_tname;
    ai->span = sp;
    return ai;
}

#define FN_TYPE_MAX 64
static FnTypeInfo g_fntypes[FN_TYPE_MAX];
static int g_n_fntypes = 0;

FnTypeInfo *fn_type_declare(const char *name, Ty ret, const char *ret_tname, Ty *params, int nparams, Span sp) {
    FnTypeInfo *ex = fn_type_find(name);
    if (ex) return ex;
    if (g_n_fntypes == FN_TYPE_MAX) {
        diag(sp, E0202, SEV_ERROR, "too many distinct function types", "reuse shapes");
        return NULL;
    }
    FnTypeInfo *fi = &g_fntypes[g_n_fntypes++];
    fi->name = name;
    fi->ret = ret;
    fi->ret_tname = ret_tname;
    fi->nparams = nparams;
    if (nparams > 8) nparams = 8;
    for (int k = 0; k < nparams; k++) fi->params[k] = params[k];
    fi->span = sp;
    return fi;
}

FnTypeInfo *fn_type_find(const char *name) {
    if (!name) return NULL;
    for (int i = 0; i < g_n_fntypes; i++)
        if (strcmp(g_fntypes[i].name, name) == 0) return &g_fntypes[i];
    return NULL;
}

int fn_type_count(void) { return g_n_fntypes; }
FnTypeInfo *fn_type_at(int i) { return (i >= 0 && i < g_n_fntypes) ? &g_fntypes[i] : NULL; }

bool ty_is_bool(Ty t) { return t == TY_BOOL; }

/* ---------------- generic helpers ---------------- */

void diag_expected(Span sp, const char *what, const char *got) {
    char msg[200];
    snprintf(msg, sizeof msg, "expected %s, got '%s'", what, got ? got : "end of input");
    diag(sp, E0101, SEV_ERROR, msg, "see spec/grammar.ebnf for the legal shapes here");
}


/* ---------------- token names (oracle for the self-host port) ---------------- */

const char *tok_name(TokKind k) {
    switch (k) {
    case TK_EOF: return "TK_EOF";
    case TK_IDENT: return "TK_IDENT";
    case TK_INT: return "TK_INT";
    case TK_FLOAT: return "TK_FLOAT";
    case TK_STR: return "TK_STR";
    case TK_FN: return "TK_FN";
    case TK_LET: return "TK_LET";
    case TK_CONST: return "TK_CONST";
    case TK_RETURN: return "TK_RETURN";
    case TK_IF: return "TK_IF";
    case TK_ELSE: return "TK_ELSE";
    case TK_WHILE: return "TK_WHILE";
    case TK_MATCH: return "TK_MATCH";
    case TK_STRUCT: return "TK_STRUCT";
    case TK_ENUM: return "TK_ENUM";
    case TK_USE: return "TK_USE";
    case TK_TIER: return "TK_TIER";
    case TK_EXTERN: return "TK_EXTERN";
    case TK_CAST: return "TK_CAST";
    case TK_TRUE: return "TK_TRUE";
    case TK_FALSE: return "TK_FALSE";
    case TK_MUT: return "TK_MUT";
    case TK_PUB: return "TK_PUB";
    case TK_LP: return "TK_LP";
    case TK_RP: return "TK_RP";
    case TK_LB: return "TK_LB";
    case TK_RB: return "TK_RB";
    case TK_BRACE_L: return "TK_BRACE_L";
    case TK_BRACE_R: return "TK_BRACE_R";
    case TK_COMMA: return "TK_COMMA";
    case TK_SEMI: return "TK_SEMI";
    case TK_COLON: return "TK_COLON";
    case TK_COLON2: return "TK_COLON2";
    case TK_DOT: return "TK_DOT";
    case TK_ARROW: return "TK_ARROW";
    case TK_FATARROW: return "TK_FATARROW";
    case TK_ASSIGN: return "TK_ASSIGN";
    case TK_ADDEQ: return "TK_ADDEQ";
    case TK_SUBEQ: return "TK_SUBEQ";
    case TK_MULEQ: return "TK_MULEQ";
    case TK_DIVEQ: return "TK_DIVEQ";
    case TK_MODEQ: return "TK_MODEQ";
    case TK_EQ: return "TK_EQ";
    case TK_NE: return "TK_NE";
    case TK_LT: return "TK_LT";
    case TK_GT: return "TK_GT";
    case TK_LE: return "TK_LE";
    case TK_GE: return "TK_GE";
    case TK_AND: return "TK_AND";
    case TK_OR: return "TK_OR";
    case TK_NOT: return "TK_NOT";
    case TK_PLUS: return "TK_PLUS";
    case TK_MINUS: return "TK_MINUS";
    case TK_STAR: return "TK_STAR";
    case TK_SLASH: return "TK_SLASH";
    case TK_PERCENT: return "TK_PERCENT";
    case TK_AMP: return "TK_AMP";
    case TK_QUESTION: return "TK_QUESTION";
    case TK_POW: return "TK_POW";
    case TK_AS: return "TK_AS";
    }
    return "TK_UNKNOWN";
}
