/* lex.c - Tripon lexer.
 * Deterministic: same bytes -> same token stream, always. */
#include "common.h"

typedef struct {
    const char *src;
    size_t len, pos;
    const char *file;
    int line, col;
    Arena *arena;
    Token *toks;
    int ntoks, cap;
} Lexer;

static const struct { const char *kw; TokKind k; } KEYWORDS[] = {
    {"fn", TK_FN}, {"let", TK_LET}, {"const", TK_CONST}, {"return", TK_RETURN},
    {"if", TK_IF}, {"else", TK_ELSE}, {"while", TK_WHILE}, {"match", TK_MATCH},
    {"struct", TK_STRUCT}, {"enum", TK_ENUM}, {"use", TK_USE}, {"tier", TK_TIER},
    {"true", TK_TRUE}, {"false", TK_FALSE},
    {"mut", TK_MUT}, {"pub", TK_PUB}, {"cast", TK_CAST},
};

static const struct { const char *op; TokKind k; } OPS[] = {
    {"::", TK_COLON2}, {"->", TK_ARROW}, {"=>", TK_FATARROW},
    {"+=", TK_ADDEQ}, {"-=", TK_SUBEQ}, {"*=", TK_MULEQ}, {"/=", TK_DIVEQ}, {"%=", TK_MODEQ},
    {"==", TK_EQ}, {"!=", TK_NE}, {"<=", TK_LE}, {">=", TK_GE},
    {"&&", TK_AND}, {"||", TK_OR},
    {"(", TK_LP}, {")", TK_RP}, {"[", TK_LB}, {"]", TK_RB},
    {"{", TK_BRACE_L}, {"}", TK_BRACE_R},
    {",", TK_COMMA}, {";", TK_SEMI}, {":", TK_COLON}, {".", TK_DOT},
    {"=", TK_ASSIGN}, {"<", TK_LT}, {">", TK_GT},
    {"!", TK_NOT}, {"+", TK_PLUS}, {"-", TK_MINUS}, {"*", TK_STAR},
    {"/", TK_SLASH}, {"%", TK_PERCENT}, {"&", TK_AMP}, {"?", TK_QUESTION},
    {"**", TK_POW},
};

static void push_tok(Lexer *lx, Token t) {
    if (lx->ntoks == lx->cap) {
        lx->cap = lx->cap ? lx->cap * 2 : 256;
        lx->toks = realloc(lx->toks, (size_t)lx->cap * sizeof(Token));
        if (!lx->toks) { fputs("ralt: out of memory\n", stderr); exit(1); }
    }
    lx->toks[lx->ntoks++] = t;
}

static char peek(Lexer *lx) { return lx->pos < lx->len ? lx->src[lx->pos] : '\0'; }
static char peek2(Lexer *lx) { return lx->pos + 1 < lx->len ? lx->src[lx->pos + 1] : '\0'; }

static void adv(Lexer *lx) {
    if (lx->pos < lx->len) {
        if (lx->src[lx->pos] == '\n') { lx->line++; lx->col = 1; }
        else lx->col++;
        lx->pos++;
    }
}

static bool ident_start(char c) {
    return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_';
}
static bool ident_char(char c) {
    return ident_start(c) || (c >= '0' && c <= '9');
}

static Span here(Lexer *lx) {
    Span s;
    s.file = lx->file;
    s.line = lx->line;
    s.col = lx->col;
    s.len = 1;
    return s;
}

static void skip_ws_comments(Lexer *lx) {
    for (;;) {
        char c = peek(lx);
        if (c == ' ' || c == '\t' || c == '\r' || c == '\n') { adv(lx); continue; }
        if (c == '/' && peek2(lx) == '/') {
            while (lx->pos < lx->len && peek(lx) != '\n') adv(lx);
            continue;
        }
        if (c == '/' && peek2(lx) == '*') {
            Span open = here(lx);
            adv(lx); adv(lx);
            bool closed = false;
            while (lx->pos < lx->len) {
                if (peek(lx) == '*' && peek2(lx) == '/') { closed = true; adv(lx); adv(lx); break; }
                adv(lx);
            }
            if (!closed) {
                diag(open, E0001, SEV_ERROR, "unterminated block comment",
                     "close the */ or keep using // line comments");
            }
            continue;
        }
        break;
    }
}

static void lex_ident(Lexer *lx) {
    size_t start = lx->pos;
    Span sp = here(lx);
    while (lx->pos < lx->len && ident_char(peek(lx))) adv(lx);
    size_t n = lx->pos - start;
    for (size_t i = 0; i < sizeof KEYWORDS / sizeof KEYWORDS[0]; i++) {
        if (strlen(KEYWORDS[i].kw) == n && memcmp(KEYWORDS[i].kw, lx->src + start, n) == 0) {
            Token t;
            memset(&t, 0, sizeof t);
            t.kind = KEYWORDS[i].k;
            t.span = sp;
            t.span.len = (int)n;
            push_tok(lx, t);
            return;
        }
    }
    Token t;
    memset(&t, 0, sizeof t);
    t.kind = TK_IDENT;
    t.span = sp;
    t.span.len = (int)n;
    t.text = arena_dupstr(lx->arena, lx->src + start, n);
    t.len = n;
    push_tok(lx, t);
}

static int digit_val(char c, int base, bool *ok) {
    *ok = true;
    if (c >= '0' && c <= '9') { int v = c - '0'; *ok = v < base; return v; }
    if (c >= 'a' && c <= 'f' && base == 16) return c - 'a' + 10;
    if (c >= 'A' && c <= 'F' && base == 16) return c - 'A' + 10;
    *ok = false;
    return 0;
}

static void lex_number(Lexer *lx) {
    size_t start = lx->pos;
    Span sp = here(lx);
    Token t;
    memset(&t, 0, sizeof t);
    t.span = sp;

    if (peek(lx) == '0' && (peek2(lx) == 'x' || peek2(lx) == 'o' || peek2(lx) == 'b')) {
        char pfx = peek2(lx);
        adv(lx); adv(lx);
        int base = pfx == 'x' ? 16 : pfx == 'o' ? 8 : 2;
        bool any = false, ok;
        long long v = 0;
        while (lx->pos < lx->len) {
            char c = peek(lx);
            if (c == '_') { adv(lx); continue; }
            int d = digit_val(c, base, &ok);
            if (!ok) break;
            v = v * base + d;
            any = true;
            adv(lx);
        }
        (void)start;
        if (!any) {
            diag(sp, E0003, SEV_ERROR, "empty number literal after 0x/0o/0b",
                 "write digits after the prefix, e.g. 0x1F");
        }
        t.kind = TK_INT;
        t.ival = v;
        t.span.len = (int)(lx->pos - start);
        push_tok(lx, t);
        return;
    }

    bool is_float = false;
    while (lx->pos < lx->len && ((peek(lx) >= '0' && peek(lx) <= '9') || peek(lx) == '_')) adv(lx);
    if (peek(lx) == '.' && peek2(lx) >= '0' && peek2(lx) <= '9') {
        is_float = true;
        adv(lx);
        while (lx->pos < lx->len && ((peek(lx) >= '0' && peek(lx) <= '9') || peek(lx) == '_')) adv(lx);
    }
    if (peek(lx) == 'e' || peek(lx) == 'E') {
        char nxt = lx->pos + 1 < lx->len ? lx->src[lx->pos + 1] : 0;
        char nn = lx->pos + 2 < lx->len ? lx->src[lx->pos + 2] : 0;
        if ((nxt >= '0' && nxt <= '9') || ((nxt == '+' || nxt == '-') && nn >= '0' && nn <= '9')) {
            is_float = true;
            adv(lx);
            if (peek(lx) == '+' || peek(lx) == '-') adv(lx);
            while (lx->pos < lx->len && peek(lx) >= '0' && peek(lx) <= '9') adv(lx);
        }
    }

    size_t end = lx->pos;
    char buf[64];
    size_t n = 0;
    for (size_t i = start; i < end && n < sizeof buf - 1; i++)
        if (lx->src[i] != '_') buf[n++] = lx->src[i];
    buf[n] = 0;

    if (is_float) {
        t.kind = TK_FLOAT;
        t.fval = strtod(buf, NULL);
    } else {
        t.kind = TK_INT;
        t.ival = strtoll(buf, NULL, 10);
    }
    t.span.len = (int)(end - start);
    push_tok(lx, t);
}

static void lex_string(Lexer *lx) {
    Span open = here(lx);
    size_t sstart = lx->pos;
    adv(lx); /* opening quote */
    char *buf = NULL;
    size_t n = 0, cap = 0;
    bool closed = false;
    while (lx->pos < lx->len) {
        char c = peek(lx);
        if (c == '"') { adv(lx); closed = true; break; }
        if (c == '\n') break;
        if (c == '\\') {
            adv(lx);
            char e = peek(lx);
            char out;
            switch (e) {
            case 'n': out = '\n'; break;
            case 't': out = '\t'; break;
            case 'r': out = '\r'; break;
            case '0': out = '\0'; break;
            case '\\': out = '\\'; break;
            case '"': out = '"'; break;
            default:
                diag(open, E0002, SEV_ERROR, "unknown escape in string",
                     "valid escapes: \\n \\t \\r \\0 \\\\ \\\"");
                out = e;
                break;
            }
            if (e != '\0') adv(lx);
            if (n + 1 > cap) { cap = cap ? cap * 2 : 16; buf = realloc(buf, cap); if (!buf) exit(1); }
            buf[n++] = out;
            continue;
        }
        if (n + 1 > cap) { cap = cap ? cap * 2 : 16; buf = realloc(buf, cap); if (!buf) exit(1); }
        buf[n++] = c;
        adv(lx);
    }
    if (!closed) {
        diag(open, E0001, SEV_ERROR, "unterminated string",
             "close it with \" on this line");
    }
    if (n + 1 > cap) { cap = n + 1; buf = realloc(buf, cap); if (!buf) exit(1); }
    buf[n] = 0;

    Token t;
    memset(&t, 0, sizeof t);
    t.kind = TK_STR;
    t.span = open;
    t.span.len = (int)(lx->pos - sstart);
    t.text = arena_dupstr(lx->arena, buf, n);
    t.len = n;
    push_tok(lx, t);
    free(buf);
}

static bool lex_op(Lexer *lx) {
    for (size_t i = 0; i < sizeof OPS / sizeof OPS[0]; i++) {
        size_t n = strlen(OPS[i].op);
        if (lx->len - lx->pos >= n && memcmp(OPS[i].op, lx->src + lx->pos, n) == 0) {
            Token t;
            memset(&t, 0, sizeof t);
            t.kind = OPS[i].k;
            t.span = here(lx);
            t.span.len = (int)n;
            for (size_t j = 0; j < n; j++) adv(lx);
            push_tok(lx, t);
            return true;
        }
    }
    return false;
}

const char *tok_kind_word(TokKind k) {
    static const char *WORDS[] = {
        "end of input", "identifier", "number", "float", "string",
        "'fn'", "'let'", "'const'", "'return'", "'if'", "'else'", "'while'",
        "'match'", "'struct'", "'enum'", "'use'", "'tier'", "'extern'", "'cast'",
        "'true'", "'false'", "'mut'", "'pub'",
        "'('", "')'", "'['", "']'", "'{'", "'}'",
        "','", "';'", "':'", "'::'", "'.'", "'->'", "'=>'",
        "'='", "'+='", "'-='", "'*='", "'/='", "'%='",
        "'=='", "'!='", "'<'", "'>'", "'<='", "'>='",
        "'&&'", "'||'", "'!'", "'+'", "'-'", "'*'", "'/'", "'%'", "'&'", "'?'", "'**'",
    };
    if (k == TK_IDENT) return "identifier";
    if (k >= TK_EOF && k <= TK_POW && WORDS[k]) return WORDS[k];
    return "token";
}

Token *lex_file(Arena *a, const char *src, size_t len, const char *file, int *ntoks) {
    Lexer lx;
    memset(&lx, 0, sizeof lx);
    lx.src = src;
    lx.len = len;
    lx.file = file;
    lx.line = 1;
    lx.col = 1;
    lx.arena = a;

    /* shebang: a leading #! line is ignored (spec: shebang-friendly) */
    if (len >= 2 && src[0] == '#' && src[1] == '!') {
        while (lx.pos < lx.len && peek(&lx) != '\n') adv(&lx);
    }

    for (;;) {
        skip_ws_comments(&lx);
        if (lx.pos >= lx.len) break;
        char c = peek(&lx);
        if (ident_start(c)) { lex_ident(&lx); continue; }
        if (c >= '0' && c <= '9') { lex_number(&lx); continue; }
        if (c == '"') { lex_string(&lx); continue; }
        if (lex_op(&lx)) continue;
        diag(here(&lx), E0002, SEV_ERROR, "unexpected character in source",
             "ASCII identifiers only; string uses double quotes; see spec/grammar.ebnf");
        adv(&lx);
    }

    Token eof;
    memset(&eof, 0, sizeof eof);
    eof.kind = TK_EOF;
    eof.span = here(&lx);
    push_tok(&lx, eof);

    *ntoks = lx.ntoks;
    return lx.toks;
}
