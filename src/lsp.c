/* lsp.c - minimal LSP server over stdio for editors/agents.
 * Handles: initialize, shutdown, exit, textDocument/didOpen, didChange (full sync),
 * publishes ralt diagnostics for the opened document. No hover yet (P3). */
#include "common.h"

static char *g_src;
static size_t g_src_len;
static const char *g_path;

/* ---------------- framing (Content-Length: n\r\n\r\n{json}) ---------------- */

static char *read_msg(size_t *len) {
    size_t cap = 64, used = 0;
    char *buf = malloc(cap);
    if (!buf) exit(1);
    for (;;) {
        int c = getchar();
        if (c == EOF) { free(buf); return NULL; }
        if (c == '\n') break;
        if (used + 1 >= cap) { cap *= 2; buf = realloc(buf, cap); if (!buf) exit(1); }
        buf[used++] = (char)c;
    }
    buf[used] = 0;
    /* find Content-Length: N */
    char *cl = strstr(buf, "Content-Length:");
    if (!cl) {
        free(buf);
        return NULL;
    }
    long n = atol(cl + strlen("Content-Length:"));
    free(buf);
    *len = (size_t)n;
    char *body = malloc((size_t)n + 1);
    if (!body) exit(1);
    size_t got = 0;
    while (got < (size_t)n) {
        int c = getchar();
        if (c == EOF) break;
        body[got++] = (char)c;
    }
    body[got] = 0;
    return body;
}

static void send_msg(const char *body) {
    printf("Content-Length: %zu\r\n\r\n%s", strlen(body), body);
    fflush(stdout);
}

/* ---------------- analysis + diagnostics conversion ---------------- */

static void analyze_source(const char *src, const char *path) {
    Arena *a = arena_new();
    int ntoks;
    Token *toks = lex_file(a, src, strlen(src), path, &ntoks);
    Decl **decls = parse_file(a, toks, ntoks, path);
    int n = 0;
    while (decls && decls[n]) n++;
    if (g_nerrors == 0) typecheck_file(a, decls, n);
    (void)a;  /* arena is process-lifetime accumulation; long-session reuse lands P3 */
}

static void publish_diagnostics(const char *uri) {
    /* size the message */
    size_t cap = 1024 + (size_t)g_ndiags * 512;
    char *body = malloc(cap);
    if (!body) exit(1);
    int n = snprintf(body, cap, "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{\"uri\":\"");
    for (const char *p = uri; *p; p++) {
        if (*p == '"') n += snprintf(body + n, (size_t)(cap - n) - 1, "\\\"");
        else body[n++] = *p;
        if ((size_t)n >= cap - 8) break;
    }
    n += snprintf(body + n, (size_t)(cap - n), "\",\"diagnostics\":[");

    for (int i = 0; i < g_ndiags && (size_t)n < cap - 64; i++) {
        Diag *d = &g_diags[i];
        const ErrEntry *e = err_lookup(d->code);
        int severity = d->sev == SEV_ERROR ? 1 : 2;   /* LSP: 1=Error 2=Warning */
        n += snprintf(body + n, (size_t)(cap - n),
                      "%s{\"range\":{\"start\":{\"line\":%d,\"character\":%d},"
                      "\"end\":{\"line\":%d,\"character\":%d}},"
                      "\"severity\":%d,\"code\":\"E%04d\",\"source\":\"ralt\"," ,
                      i ? "," : "",
                      d->span.line - 1, d->span.col - 1,
                      d->span.line - 1, d->span.col - 1 + d->span.len,
                      severity, d->code);
        /* message */
        n += snprintf(body + n, (size_t)(cap - n), "\"message\":\"");
        for (const char *p = d->msg; *p && (size_t)n < cap - 12; p++) {
            if (*p == '"' || *p == '\\') body[n++] = '\\';
            body[n++] = *p;
        }
        n += snprintf(body + n, (size_t)(cap - n), "\"");
        /* hint as markdown "documentation"... LSP has no hint field; append */
        if (d->hint[0] && (size_t)n < cap - 256) {
            n += snprintf(body + n, (size_t)(cap - n), " - hint: ");
            for (const char *p = e->hint; *p && (size_t)n < cap - 12; p++) {
                if (*p == '"' || *p == '\\') body[n++] = '\\';
                body[n++] = *p;
            }
        }
        n += snprintf(body + n, (size_t)(cap - n), "}");
    }
    n += snprintf(body + n, (size_t)(cap - n), "]}}");
    send_msg(body);
    free(body);
}

static void handle_message(const char *msg) {
    /* extract "method" */
    const char *method = strstr(msg, "\"method\":\"");
    if (!method) return;
    method += strlen("\"method\":\"");
    const char *mend = strchr(method, '"');
    if (!mend) return;
    size_t mlen = (size_t)(mend - method);
    char mbuf[64];
    mlen = mlen < sizeof mbuf - 1 ? mlen : sizeof mbuf - 1;
    memcpy(mbuf, method, mlen);
    mbuf[mlen] = 0;

    const char *idmark = strstr(msg, "\"id\":");
    long id = idmark ? atol(idmark + strlen("\"id\":")) : 1;
    char idbuf[32];
    snprintf(idbuf, sizeof idbuf, "%ld", id);

    if (strcmp(mbuf, "initialize") == 0) {
        size_t r = 512;
        char *reply = malloc(r);
        if (!reply) exit(1);
        snprintf(reply, r,
                 "{\"jsonrpc\":\"2.0\",\"id\":%s,\"result\":{"
                 "\"capabilities\":{"
                 "\"textDocumentSync\":1,"
                 "\"diagnosticProvider\":{}"
                 "},\"serverInfo\":{\"name\":\"ralt\",\"version\":\"0.1\"}}}", idbuf);
        send_msg(reply);
        free(reply);
        return;
    }
    if (strcmp(mbuf, "shutdown") == 0) {
        size_t r = 128;
        char *reply = malloc(r);
        if (!reply) exit(1);
        snprintf(reply, r, "{\"jsonrpc\":\"2.0\",\"id\":%s,\"result\":null}", idbuf);
        send_msg(reply);
        free(reply);
        return;
    }
    if (strcmp(mbuf, "exit") == 0) {
        exit(0);
    }
    if (strcmp(mbuf, "textDocument/didOpen") == 0 ||
        strcmp(mbuf, "textDocument/didChange") == 0) {
        /* dig out uri + text fields naive but stable */
        const char *uri = strstr(msg, "\"uri\":\"");
        const char *text = strstr(msg, "\"text\":\"");
        if (uri && text) {
            uri += strlen("\"uri\":\"");
            const char *ue = strchr(uri, '"');
            text += strlen("\"text\":\"");
            size_t tcap = strlen(text) + 8;
            char *raw = malloc(tcap);
            if (!raw) exit(1);
            size_t j = 0;
            for (const char *p = text; *p; p++) {
                if (*p == '\\' && p[1] == 'n') { raw[j++] = '\n'; p++; continue; }
                if (*p == '\\' && p[1] == 't') { raw[j++] = '\t'; p++; continue; }
                if (*p == '\\' && p[1] == 'r') { raw[j++] = '\r'; p++; continue; }
                if (*p == '\\' && p[1] == 0) break;
                if (*p == '\\' && (p[1] == '"' || p[1] == '\\')) { raw[j++] = p[1]; p++; continue; }
                if (*p == '"' && *(p + 1) != '\0' && strchr(p + 1, '"') == p + 1) break;
                if (*p == '"') break;
                raw[j++] = *p;
            }
            raw[j] = 0;
            size_t uelen = ue ? (size_t)(ue - uri) : strlen(uri);
            char *uribuf = malloc(uelen + 1);
            if (!uribuf) exit(1);
            memcpy(uribuf, uri, uelen);
            uribuf[uelen] = 0;
            free(g_src);
            g_src = raw;
            g_src_len = j;
            g_path = uribuf;
            analyze_source(g_src, uribuf);
            publish_diagnostics(uribuf);
        }
        return;
    }
}

void lsp_serve(void) {
    g_src = NULL;
    g_src_len = 0;
    g_path = NULL;
    for (;;) {
        size_t len;
        char *body = read_msg(&len);
        if (!body) break;
        handle_message(body);
        free(body);
    }
}
