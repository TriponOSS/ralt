/* diag.c - collect diagnostics, print human or JSON, error-code table.
 * Mirrors spec/errors.csv (regen script comes with self-host). */
#include "common.h"

Diag *g_diags;
int g_ndiags, g_ncap;
int g_nerrors, g_nwarns;

const ErrEntry *err_lookup(int code) {
    static const ErrEntry TABLE[] = {
        {E0001, SEV_ERROR, "unterminated-string", "string must close with a double quote on the same line"},
        {E0002, SEV_ERROR, "invalid-character", "ASCII identifiers only; table in spec/tripon.md"},
        {E0003, SEV_ERROR, "bad-number-literal", "forms: 123, 0x1F, 0o17, 0b1010, 3.14, 1e-9"},
        {E0101, SEV_ERROR, "unexpected-token", "see spec/grammar.ebnf for what is legal here"},
        {E0102, SEV_ERROR, "missing-token", "expected the token named in the message"},
        {E0201, SEV_ERROR, "unknown-identifier", "define it, use the right module, or fix spelling"},
        {E0202, SEV_ERROR, "type-mismatch", "types must match exactly; no implicit conversion exists; use cast<T>(x)"},
        {E0203, SEV_ERROR, "mutability-required", "declared const but reassigned; switch to let"},
        {E0204, SEV_ERROR, "no-null", "null and undefined do not exist; use opt<T>"},
        {E0205, SEV_ERROR, "unhandled-result", "Result value ignored; spread with ? or match"},
        {E0206, SEV_ERROR, "non-exhaustive-match", "match must cover every enum variant or add a deliberate _ arm"},
        {E0207, SEV_ERROR, "implicit-conversion-denied", "no implicit conversions exist; use cast<T>(x) for exact or explicit lossy casts"},
        {E0212, SEV_ERROR, "duplicate-match-arm", "remove or reorder the repeated arm; match arms are checked top to bottom"},
        {E0301, SEV_ERROR, "tier-violation", "feature requires a higher tier; raise the tier target or rewrite the call"},
        {E0302, SEV_ERROR, "tier-not-declared", "add a top-of-file use tier <name>; statement"},
        {E0501, SEV_ERROR, "entry-point-missing", "define fn main() -> i32"},
        {E9001, SEV_ERROR, "integer-overflow-trap", "arithmetic overflow is a defined trap; pass -fast to wrap"},
        {E9002, SEV_ERROR, "index-out-of-bounds", "indexing is bounds-checked everywhere; slice.len() before indexing"},
        {E9003, SEV_ERROR, "division-by-zero-trap", "div and mod by zero are defined traps; guard the divisor"},
        {E0601, SEV_WARN,  "unused-binding", "prefix with _ to mute"},
        {E0602, SEV_WARN,  "unreachable-code", "unreachable after earlier return/branch"},
        {E0603, SEV_WARN,  "shadowing", "name shadows an existing binding in scope; rename"},
    };
    static const ErrEntry UNKNOWN = {0, SEV_ERROR, "internal", "report this to the Tripon repo with a minimal repro"};
    for (size_t i = 0; i < sizeof TABLE / sizeof TABLE[0]; i++)
        if (TABLE[i].code == code) return &TABLE[i];
    return &UNKNOWN;
}

void diag(Span sp, int code, Sev sev, const char *msg, const char *hint) {
    if (g_ndiags == g_ncap) {
        g_ncap = g_ncap ? g_ncap * 2 : 16;
        g_diags = realloc(g_diags, (size_t)g_ncap * sizeof(Diag));
        if (!g_diags) { fputs("ralt: out of memory\n", stderr); exit(1); }
    }
    Diag *d = &g_diags[g_ndiags++];
    memset(d, 0, sizeof *d);
    d->span = sp;
    d->code = code;
    d->sev = sev;
    snprintf(d->msg, sizeof d->msg, "%s", msg ? msg : "");
    snprintf(d->hint, sizeof d->hint, "%s", hint ? hint : "");
    if (sev == SEV_ERROR) g_nerrors++;
    if (sev == SEV_WARN) g_nwarns++;
}

static void json_escape(const char *s, FILE *out) {
    for (; *s; s++) {
        unsigned char c = (unsigned char)*s;
        if (c == '"' || c == '\\') fprintf(out, "\\%c", c);
        else if (c == '\n') fputs("\\n", out);
        else if (c == '\t') fputs("\\t", out);
        else if (c < 0x20) fprintf(out, "\\u%04x", c);
        else fputc(c, out);
    }
}

static void json_str(const char *s, FILE *out) {
    fputc('"', out);
    json_escape(s ? s : "", out);
    fputc('"', out);
}

static const char *sev_word(Sev s) {
    switch (s) {
    case SEV_ERROR: return "error";
    case SEV_WARN:  return "warn";
    default:        return "note";
    }
}

void print_diags(bool json) {
    if (json) {
        if (g_ndiags == 0) {
            puts("[]");
            return;
        }
        fputs("[", stdout);
        for (int i = 0; i < g_ndiags; i++) {
            Diag *d = &g_diags[i];
            const ErrEntry *e = err_lookup(d->code);
            if (i) fputs(",", stdout);
            fprintf(stdout, "\n  { \"code\": \"E%04d\", \"kind\": \"%s\", \"name\": \"%s\", ",
                    d->code, sev_word(d->sev), e->name);
            fputs("\"file\": ", stdout); json_str(d->span.file, stdout);
            fprintf(stdout, ", \"line\": %d, \"col\": %d, \"len\": %d",
                    d->span.line, d->span.col, d->span.len);
            fputs(", \"msg\": ", stdout); json_str(d->msg, stdout);
            fputs(", \"hint\": ", stdout); json_str(d->hint, stdout);
            fputs(" }", stdout);
        }
        fputs("\n]\n", stdout);
    } else {
        for (int i = 0; i < g_ndiags; i++) {
            Diag *d = &g_diags[i];
            fprintf(stderr, "%s:%d:%d: %s: %s\n",
                    d->span.file, d->span.line, d->span.col, sev_word(d->sev), d->msg);
            if (d->code) {
                const ErrEntry *e = err_lookup(d->code);
                fprintf(stderr, "  [E%04d %s] %s\n", d->code, e->name, e->hint);
            }
        }
    }
}

