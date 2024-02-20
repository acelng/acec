// Copyright 2024 Luca Mazza
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// Created by Luca Mazza on 2024/2/1.
//

#include "acec.h"
#include "../../definitions/syntax.h"
#include "../../definitions/errmsg.h"

/// Input file
static File *current_file;

/// List of all input files
static File **input_files;

/// If the curr pos is at start of line
static bool at_sol;

/// If the current pos follows space
static bool has_space;

/// Reports error & exit
void error(char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    fprintf(stderr, "\n");
    exit(1);
}

/// Formatted error reporting
///
/// example.ace:10: x=y+1;
///                   ^ <error message>
static void verror_at(char *filename, char *input, int line_no, char *loc, char *fmt, va_list ap) {
    // find a line containing `loc`
    char *line = loc;
    while (input < line && line[-1] != ES_NL) line--;
    char *end = loc;
    while (*end && *end != ES_NL) end++;
    // print out line
    int indent = fprintf(stderr, "%s:%d: ", filename, line_no);
    fprintf(stderr, "%.*s\n", (int) (end - line), line);
    // show error msg
    int pos = display_width(line, loc - line) + indent;
    fprintf(stderr, "%*s", pos, "");
    fprintf(stderr, "^ ");
    vfprintf(stderr, fmt, ap);
    fprintf(stderr, "\n");
}

/// Reports an error at a given location
void error_at(char *loc, char *fmt, ...) {
    int line_no = 1;
    for (char *p = current_file->contents; p < loc; p++) if (*p == ES_NL) line_no++;
    va_list ap;
    va_start(ap, fmt);
    verror_at(current_file->name, current_file->contents, line_no, loc, fmt, ap);
    exit(1);
}

/// Reports an error at a given token
void error_tok(Token *tok, char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    verror_at(tok->file->name, tok->file->contents, tok->line_no, tok->loc, fmt, ap);
    exit(1);
}

/// Reports a warning at a given token
void warn_tok(Token *tok, char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    verror_at(tok->file->name, tok->file->contents, tok->line_no, tok->loc, fmt, ap);
    va_end(ap);
}

/// Consumes current token if it matches `op`
bool equal(Token *tok, char *op) {
    return memcmp(tok->loc, op, tok->len) == 0 && op[tok->len] == ES_NUL;
}

/// Ensures current token is `op`
Token *skip(Token *tok, char *op) {
    if (!equal(tok, op)) error_tok(tok, EXPECTED_STR, op);
    return tok->next;
}

/// Consumes current token if it matches `op`
bool consume(Token **rest, Token *tok, char *str) {
    if (equal(tok, str)) {
        *rest = tok->next;
        return true;
    }
    *rest = tok;
    return false;
}

/// Create a new token
static Token *new_token(TokenKind kind, char *start, char *end) {
    Token *tok = calloc(1, sizeof(Token));
    tok->kind = kind;
    tok->loc = start;
    tok->len = end - start;
    tok->file = current_file;
    tok->filename = current_file->display_name;
    tok->at_sol = at_sol;
    tok->has_space = has_space;
    at_sol = has_space = false;
    return tok;
}

/// Returns true if p starts with q
static bool starts_with(char *p, char *q) {
    return strncmp(p, q, strlen(q)) == 0;
}

/// Read an identifier and returns the len
/// If p not pointing to an id return 0
static int read_id(char *start) {
    char *p = start;
    uint32_t c = decode_utf8(&p, p);
    if (!is_id1(c)) return 0;

    for (;;) {
        char *q;
        c = decode_utf8(&q, p);
        if (!is_id2(c)) return p - start;
        p = q;
    }
}

/// Returns the char code of a hex digit
static int from_hex(char c) {
    if ('0' <= c && c <= '9') return c - '0';
    if ('a' <= c && c <= 'f') return c - 'a' + 10;
    return c - 'A' + 10;
}

/// Read a punctuator token from p and return len
static int read_punct(char *p) {
    static char *kw[] = {
            OP_ASSIGN_SHL, OP_ASSIGN_SHR, PT_VARARGS, OP_LOG_EQ, OP_LOG_NE, OP_LOG_LE,
            OP_LOG_GE, PT_ARROW, OP_ASSIGN_ADD,OP_ASSIGN_SUB, OP_ASSIGN_MUL, OP_ASSIGN_DIV,
            OP_INCR, OP_DECR, OP_ASSIGN_MOD, OP_ASSIGN_AND, OP_ASSIGN_OR, OP_ASSIGN_XOR,
            OP_LOG_AND, OP_LOG_OR, OP_SHL, OP_SHR, PP_POUND_POUND,
    };
    for (int i = 0; i < sizeof(kw) / sizeof(kw[0]); i++) if (starts_with(p, kw[i])) return strlen(kw[i]);
    return ispunct(*p) ? 1 : 0;
}

/// Returns true if p is a keyword
static bool is_keyword(Token *tok) {
    static HashMap map;

    if (map.capacity == 0) {
        static char *kw[] = {
                KW_RETURN, KW_IF, KW_ELSE, KW_FOR, KW_WHILE, KW_INT, KW_SIZEOF,
                KW_CHAR, KW_STRUCT, KW_UNION, KW_SHORT, KW_LONG, KW_VOID, KW_TYPEDEF,
                KW_BOOL, KW_ENUM, KW_STATIC, KW_GOTO, KW_BREAK, KW_CONTINUE,
                KW_SWITCH, KW_CASE, KW_DEFAULT, KW_EXTERN, PP_ALIGNOF, PP_ALIGNAS,
                KW_DO, KW_SIGNED, KW_UNSIGNED, KW_CONST, KW_VOLATILE, KW_REGISTER,
                KW_RESTRICT, PP_NORETURN, KW_FLOAT, KW_DOUBLE, KW_TYPEOF,
                PP_ASM, PP_THREAD_LOCAL, PP_THREAD, PP_ATOMIC
        };

        for (int i = 0; i < sizeof(kw) / sizeof(*kw); i++)
            hashmap_put(&map, kw[i], (void *)1);
    }

    return hashmap_get_wlen(&map, tok->loc, tok->len);
}

/// Read an escaped character and return the char code
static int read_escaped_char(char **new_pos, char *p) {
    if ('0' <= *p && *p <= '7') {
        /// read octal num
        int c = *p++ - '0';
        if ('0' <= *p && *p <= '7') {
            c = (c << 3) + (*p++ - '0');
            if ('0' <= *p && *p <= '7') c = (c << 3) + (*p++ - '0');
        }
        *new_pos = p;
        return c;
    }

    if (*p == 'x') {
        /// Read hex num
        p++;
        if (!isxdigit(*p)) error_at(p, INV_HEX_ESC_SEQ);
        int c = 0;
        for (; isxdigit(*p); p++) c = (c << 4) + from_hex(*p);
        *new_pos = p;
        return c;
    }

    *new_pos = p + 1;

    // Escape sequences are defined using themselves here. E.g.
    // '\n' is implemented using '\n'. This tautological definition
    // works because the compiler that compiles our compiler knows
    // what '\n' actually is. In other words, we "inherit" the ASCII
    // code of '\n' from the compiler that compiles our compiler,
    // so we don't have to teach the actual code here.
    switch (*p) {
        case 'a': return ES_ALERT;
        case 'b': return ES_BACKSPACE;
        case 't': return ES_TAB;
        case 'n': return ES_NL;
        case 'v': return ES_VTAB;
        case 'f': return ES_FORM_FEED;
        case 'r': return ES_CR;
        default: return *p;
    }
}

/// Find a closing double quote
static char *string_literal_end(char *p) {
    char *start = p;
    for (; *p != PT_QUOTE; p++) {
        if (*p == ES_NL || *p == ES_NUL) error_at(start, UNT_STR);
        if (*p == PT_BACKSLASH) p++;
    }
    return p;
}

/// Read a UTF-8-encoded string literal and decode it.
static Token *read_string_literal(char *start, char *quote) {
    char *end = string_literal_end(quote + 1);
    char *buf = calloc(1, end - quote);
    int len = 0;
    for (char *p = quote + 1; p < end;) {
        if (*p == PT_BACKSLASH) buf[len++] = read_escaped_char(&p, p + 1);
        else buf[len++] = *p++;
    }
    Token *tok = new_token(TK_STR, start, end + 1);
    tok->ty = array_of(ty_char, len + 1);
    tok->str = buf;
    return tok;
}

/// Read a UTF-8-encoded string literal and transcode it in UTF-16.
///
/// UTF-16 is yet another variable-width encoding for Unicode. Code
/// points smaller than U+10000 are encoded in 2 bytes. Code points
/// equal to or larger than that are encoded in 4 bytes. Each 2 bytes
/// in the 4 byte sequence is called "surrogate", and a 4 byte sequence
/// is called a "surrogate pair".
static Token *read_utf16_string_literal(char *start, char *quote) {
    char *end = string_literal_end(quote + 1);
    uint16_t *buf = calloc(2, end - start);
    int len = 0;
    for (char *p = quote + 1; p < end;) {
        if (*p == PT_BACKSLASH) {
            buf[len++] = read_escaped_char(&p, p + 1);
            continue;
        }
        uint32_t c = decode_utf8(&p, p);
        if (c < 0x10000)
            // Encode a code point in 2 bytes.
            buf[len++] = c;
        else {
            // Encode a code point in 4 bytes.
            c -= 0x10000;
            buf[len++] = 0xd800 + ((c >> 10) & 0x3ff);
            buf[len++] = 0xdc00 + (c & 0x3ff);
        }
    }
    Token *tok = new_token(TK_STR, start, end + 1);
    tok->ty = array_of(ty_ushort, len + 1);
    tok->str = (char *)buf;
    return tok;
}

/// Read a UTF-8-encoded string literal and transcode it in UTF-32.
///
/// UTF-32 is a fixed-width encoding for Unicode. Each code point is
/// encoded in 4 bytes.
static Token *read_utf32_string_literal(char *start, char *quote, Type *ty) {
    char *end = string_literal_end(quote + 1);
    uint32_t *buf = calloc(4, end - quote);
    int len = 0;

    for (char *p = quote + 1; p < end;) {
        if (*p == PT_BACKSLASH) buf[len++] = read_escaped_char(&p, p + 1);
        else buf[len++] = decode_utf8(&p, p);
    }
    Token *tok = new_token(TK_STR, start, end + 1);
    tok->ty = array_of(ty, len + 1);
    tok->str = (char *)buf;
    return tok;
}

/// Read a character literal and decode it.
static Token *read_char_literal(char *start, char *quote, Type *ty) {
    char *p = quote + 1;
    if (*p == ES_NUL) error_at(start, UNT_CHAR);
    int c;
    if (*p == PT_BACKSLASH) c = read_escaped_char(&p, p + 1);
    else c = decode_utf8(&p, p);
    char *end = strchr(p, '\'');
    if (!end) error_at(p, UNT_CHAR);
    Token *tok = new_token(TK_NUM, start, end + 1);
    tok->val = c;
    tok->ty = ty;
    return tok;
}

/// Convert a pp-number token to a regular number token.
static bool convert_pp_int(Token *tok) {
    char *p = tok->loc;
    // Read a binary, octal, decimal or hexadecimal number.
    int base = 10;
    if (!strncasecmp(p, "0x", 2) && isxdigit(p[2])) {
        p += 2;
        base = 16;
    } else if (!strncasecmp(p, "0b", 2) && (p[2] == '0' || p[2] == '1')) {
        p += 2;
        base = 2;
    } else if (*p == '0') {
        base = 8;
    }
    int64_t val = strtoul(p, &p, base);
    // Read U, L or LL suffixes.
    bool l = false;
    bool u = false;
    if (starts_with(p, "LLU") || starts_with(p, "LLu") ||
        starts_with(p, "llU") || starts_with(p, "llu") ||
        starts_with(p, "ULL") || starts_with(p, "Ull") ||
        starts_with(p, "uLL") || starts_with(p, "ull")) {
        p += 3;
        l = u = true;
    } else if (!strncasecmp(p, "lu", 2) || !strncasecmp(p, "ul", 2)) {
        p += 2;
        l = u = true;
    } else if (starts_with(p, "LL") || starts_with(p, "ll")) {
        p += 2;
        l = true;
    } else if (*p == 'L' || *p == 'l') {
        p++;
        l = true;
    } else if (*p == 'U' || *p == 'u') {
        p++;
        u = true;
    }
    if (p != tok->loc + tok->len) return false;
    // Infer a type.
    Type *ty;
    if (base == 10) {
        if (l && u) ty = ty_ulong;
        else if (l) ty = ty_long;
        else if (u) ty = (val >> 32) ? ty_ulong : ty_uint;
        else ty = (val >> 31) ? ty_long : ty_int;
    } else {
        if (l && u) ty = ty_ulong;
        else if (l) ty = (val >> 63) ? ty_ulong : ty_long;
        else if (u) ty = (val >> 32) ? ty_ulong : ty_uint;
        else if (val >> 63) ty = ty_ulong;
        else if (val >> 32) ty = ty_long;
        else if (val >> 31) ty = ty_uint;
        else ty = ty_int;
    }
    tok->kind = TK_NUM;
    tok->val = val;
    tok->ty = ty;
    return true;
}

/// The definition of the numeric literal at the preprocessing stage
/// is more relaxed than the definition of that at the later stages.
/// In order to handle that, a numeric literal is tokenized as a
/// "pp-number" token first and then converted to a regular number
/// token after preprocessing.
///
/// This function converts a pp-number token to a regular number token.
static void convert_pp_number(Token *tok) {
    // Try to parse as an integer constant.
    if (convert_pp_int(tok)) return;
    // If it's not an integer, it must be a floating point constant.
    char *end;
    long double val = strtold(tok->loc, &end);
    Type *ty;
    if (*end == 'f' || *end == 'F') {
        ty = ty_float;
        end++;
    } else if (*end == 'l' || *end == 'L') {
        ty = ty_ldouble;
        end++;
    } else {
        ty = ty_double;
    }
    if (tok->loc + tok->len != end) error_tok(tok, INV_NUM_CONST);
    tok->kind = TK_NUM;
    tok->fval = val;
    tok->ty = ty;
}

/// Convert all pp-number tokens to regular number tokens.
void convert_pp_tokens(Token *tok) {
    for (Token *t = tok; t->kind != TK_EOF; t = t->next) {
        if (is_keyword(t)) t->kind = TK_KEYWORD;
        else if (t->kind == TK_PP_NUM) convert_pp_number(t);
    }
}

/// Initialize line info for all tokens.
static void add_line_numbers(Token *tok) {
    char *p = current_file->contents;
    int n = 1;
    do {
        if (p == tok->loc) {
            tok->line_no = n;
            tok = tok->next;
        }
        if (*p == ES_NL) n++;
    } while (*p++);
}

/// Tokenize a string literal and returns a new token.
Token *tokenize_string_literal(Token *tok, Type *basety) {
    Token *t;
    if (basety->size == 2) t = read_utf16_string_literal(tok->loc, tok->loc);
    else t = read_utf32_string_literal(tok->loc, tok->loc, basety);
    t->next = tok->next;
    return t;
}

/// Tokenize a given string and returns new tokens.
Token *tokenize(File *file) {
    current_file = file;
    char *p = file->contents;
    Token head = {};
    Token *cur = &head;
    at_sol = true;
    has_space = false;
    while (*p) {
        // Skip line comments.
        if (starts_with(p, INLINE_COMMENT)) {
            p += 2;
            while (*p != ES_NL)
                p++;
            has_space = true;
            continue;
        }
        // Skip block comments.
        if (starts_with(p, BLOCK_COMMENT_START)) {
            char *q = strstr(p + 2, BLOCK_COMMENT_END);
            if (!q) error_at(p, UNT_BCOMMENT);
            p = q + 2;
            has_space = true;
            continue;
        }
        // Skip newline.
        if (*p == ES_NL) {
            p++;
            at_sol = true;
            has_space = false;
            continue;
        }
        // Skip whitespace characters.
        if (isspace(*p)) {
            p++;
            has_space = true;
            continue;
        }
        // Numeric literal
        if (isdigit(*p) || (*p == *PT_POINT && isdigit(p[1]))) {
            char *q = p++;
            for (;;) {
                if (p[0] && p[1] && strchr("eEpP", p[0]) && strchr("+-", p[1])) p += 2;
                else if (isalnum(*p) || *p == *PT_POINT) p++;
                else break;
            }
            cur = cur->next = new_token(TK_PP_NUM, q, p);
            continue;
        }
        // String literal
        if (*p == PT_QUOTE) {
            cur = cur->next = read_string_literal(p, p);
            p += cur->len;
            continue;
        }
        // UTF-8 string literal
        if (starts_with(p, "u8\"")) {
            cur = cur->next = read_string_literal(p, p + 2);
            p += cur->len;
            continue;
        }
        // UTF-16 string literal
        if (starts_with(p, "u\"")) {
            cur = cur->next = read_utf16_string_literal(p, p + 1);
            p += cur->len;
            continue;
        }
        // Wide string literal
        if (starts_with(p, "L\"")) {
            cur = cur->next = read_utf32_string_literal(p, p + 1, ty_int);
            p += cur->len;
            continue;
        }
        // UTF-32 string literal
        if (starts_with(p, "U\"")) {
            cur = cur->next = read_utf32_string_literal(p, p + 1, ty_uint);
            p += cur->len;
            continue;
        }
        // Character literal
        if (*p == '\'') {
            cur = cur->next = read_char_literal(p, p, ty_int);
            cur->val = (char)cur->val;
            p += cur->len;
            continue;
        }
        // UTF-16 character literal
        if (starts_with(p, "u'")) {
            cur = cur->next = read_char_literal(p, p + 1, ty_ushort);
            cur->val &= 0xffff;
            p += cur->len;
            continue;
        }
        // Wide character literal
        if (starts_with(p, "L'")) {
            cur = cur->next = read_char_literal(p, p + 1, ty_int);
            p += cur->len;
            continue;
        }
        // UTF-32 character literal
        if (starts_with(p, "U'")) {
            cur = cur->next = read_char_literal(p, p + 1, ty_uint);
            p += cur->len;
            continue;
        }
        // Identifier or keyword
        int ident_len = read_id(p);
        if (ident_len) {
            cur = cur->next = new_token(TK_IDENT, p, p + ident_len);
            p += cur->len;
            continue;
        }
        // Punctuators
        int punct_len = read_punct(p);
        if (punct_len) {
            cur = cur->next = new_token(TK_PUNCT, p, p + punct_len);
            p += cur->len;
            continue;
        }
        error_at(p, INV_TOK);
    }
    cur = cur->next = new_token(TK_EOF, p, p);
    add_line_numbers(head.next);
    return head.next;
}

/// Returns the contents of a given file.
static char *read_file(char *path) {
    FILE *fp;
    if (strcmp(path, OP_SUB) == 0) {
        // By convention, read from stdin if a given filename is "-".
        fp = stdin;
    } else {
        fp = fopen(path, "r");
        if (!fp) return NULL;
    }
    char *buf;
    size_t buflen;
    FILE *out = open_memstream(&buf, &buflen);
    // Read the entire file.
    for (;;) {
        char buf2[4096];
        int n = fread(buf2, 1, sizeof(buf2), fp);
        if (n == 0) break;
        fwrite(buf2, 1, n, out);
    }
    if (fp != stdin) fclose(fp);
    // Make sure that the last line is properly terminated with '\n'.
    fflush(out);
    if (buflen == 0 || buf[buflen - 1] != ES_NL) fputc(ES_NL, out);
    fputc(ES_NUL, out);
    fclose(out);
    return buf;
}

/// Returns the list of input files.
File **get_input_files(void) {
    return input_files;
}

/// Creates a new file.
File *new_file(char *name, int file_no, char *contents) {
    File *file = calloc(1, sizeof(File));
    file->name = name;
    file->display_name = name;
    file->file_no = file_no;
    file->contents = contents;
    return file;
}

/// Replaces \r or \r\n with \n.
static void canonicalize_newline(char *p) {
    int i = 0, j = 0;
    while (p[i]) {
        if (p[i] == ES_CR && p[i + 1] == ES_NL) {
            i += 2;
            p[j++] = ES_NL;
        } else if (p[i] == ES_CR) {
            i++;
            p[j++] = ES_NL;
        } else {
            p[j++] = p[i++];
        }
    }
    p[j] = ES_NUL;
}

/// Removes backslashes followed by a newline.
static void remove_backslash_newline(char *p) {
    int i = 0, j = 0;
    // We want to keep the number of newline characters so that
    // the logical line number matches the physical one.
    // This counter maintains the number of newlines we have removed.
    int n = 0;
    while (p[i]) {
        if (p[i] == PT_BACKSLASH && p[i + 1] == ES_NL) {
            i += 2;
            n++;
        } else if (p[i] == ES_NL) {
            p[j++] = p[i++];
            for (; n > 0; n--)
                p[j++] = ES_NL;
        } else {
            p[j++] = p[i++];
        }
    }
    for (; n > 0; n--) p[j++] = ES_NL;
    p[j] = ES_NUL;
}

/// Read a universal character escape sequence.
static uint32_t read_universal_char(char *p, int len) {
    uint32_t c = 0;
    for (int i = 0; i < len; i++) {
        if (!isxdigit(p[i])) return 0;
        c = (c << 4) | from_hex(p[i]);
    }
    return c;
}

/// Replace \u or \U escape sequences with corresponding UTF-8 bytes.
static void convert_universal_chars(char *p) {
    char *q = p;
    while (*p) {
        if (starts_with(p, "\\u")) {
            uint32_t c = read_universal_char(p + 2, 4);
            if (c) {
                p += 6;
                q += encode_utf8(q, c);
            } else {
                *q++ = *p++;
            }
        } else if (starts_with(p, "\\U")) {
            uint32_t c = read_universal_char(p + 2, 8);
            if (c) {
                p += 10;
                q += encode_utf8(q, c);
            } else {
                *q++ = *p++;
            }
        } else if (p[0] == PT_BACKSLASH) {
            *q++ = *p++;
            *q++ = *p++;
        } else {
            *q++ = *p++;
        }
    }
    *q = ES_NUL;
}

/// Tokenizes a given file.
Token *tokenize_file(char *path) {
    char *p = read_file(path);
    if (!p) return NULL;
    // UTF-8 texts may start with a 3-byte "BOM" marker sequence.
    // If exists, just skip them because they are useless bytes.
    // (It is actually not recommended to add BOM markers to UTF-8
    // texts, but it's not uncommon particularly on Windows...)
    if (!memcmp(p, "\xef\xbb\xbf", 3)) p += 3;
    canonicalize_newline(p);
    remove_backslash_newline(p);
    convert_universal_chars(p);
    // Save the filename for assembler .file directive.
    static int file_no;
    File *file = new_file(path, file_no + 1, p);
    // Save the filename for assembler .file directive.
    input_files = realloc(input_files, sizeof(char *) * (file_no + 2));
    input_files[file_no] = file;
    input_files[file_no + 1] = NULL;
    file_no++;
    return tokenize(file);
}
