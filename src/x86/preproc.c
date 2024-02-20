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

/// Type definition for a macro parameter
typedef struct MacroParam MacroParam;

/// Type definition for a macro argument
typedef struct MacroArg MacroArg;

/// Type definition for a macro
typedef struct Macro Macro;

/// Type definition for a macro handler function
typedef Token *macro_handler_fn(Token *);

/// Type definition for nested conditions
typedef struct CondIncl CondIncl;

/// Type definition for a hideset
typedef struct Hideset Hideset;

/// Structure for a macro parameter
struct MacroParam {
    MacroParam *next;
    char *name;
};

/// Structure for a macro argument
struct MacroArg {
    MacroArg *next;
    char *name;
    bool *is_va_args;
    Token *tok;
};

/// Structure for a macro
struct Macro {
    char *name;
    bool is_objlike; // Object-like or Function-like
    MacroParam *params;
    char *va_args_name;
    Token *body;
    macro_handler_fn *handler;
};

/// Structure for conditional inclusion
struct CondIncl {
    CondIncl *next;
    enum {IN_THEN, IN_ELIF, IN_ELSE } ctx;
    Token *tok;
    bool included;
};

/// Structure for a hideset
struct Hideset {
    Hideset *next;
    char *name;
};

/// Macros
static HashMap macros;

/// Nested conditions
static CondIncl *cond_incl;

/// Pragma once macros
static HashMap pragma_once;

/// Next idx included
static int include_next_idx;

/// Preprocesses a token
static Token *preprocess2(Token *tok);

/// Finds a macro given a token
static Macro *find_macro(Token *tok);

/// Checks if a token is a hashtag
static bool is_hash(Token *tok) {
    return tok->at_sol && equal(tok, PP_POUND);
}

/// Skips a line while they have extraneous tokens at sol.
/// I.e. `#include` directives allow extraneous tokens.
static Token *skip_line(Token *tok) {
    if (tok->at_sol) return tok;
    warn_tok(tok, UNEXPECTED_TOKEN);
    while (tok->at_sol) tok = tok->next;
    return tok;
}

/// Copies a token
static Token *copy_token(Token *tok) {
    Token *t = calloc(1, sizeof(Token));
    *t = *tok;
    t->next = NULL;
    return t;
}

/// Creates a new EOF token given another token
static Token *new_eof(Token *tok) {
    Token *t = copy_token(tok);
    t->kind = TK_EOF;
    t->len = 0;
    return t;
}

/// Creates a new hideset
static Hideset *new_hideset(char *name) {
    Hideset *h = calloc(1, sizeof(Hideset));
    h->name = name;
    return h;
}

/// Creates a new hideset union given 2 hidesets
static Hideset *hideset_union(Hideset *h1, Hideset *h2) {
    Hideset head = {};
    Hideset *cur = &head;
    for (; h1; h1 = h1->next) cur = cur->next = new_hideset(h1->name);
    cur->next = h2;
    return head.next;
}

/// Checks if a hideset contains a name
static bool hideset_contains(Hideset *h, char *s, int len) {
    for (; h; h = h->next) if (strlen(h->name) == len && !strncmp(h->name, s, len)) return true;
    return false;
}

/// Creates a new hideset intersection
static Hideset *hideset_intersection(Hideset *h1, Hideset *h2) {
    Hideset head = {};
    Hideset *cur = &head;
    for (; h1; h1 = h1->next)
        if (hideset_contains(h2, h1->name, strlen(h1->name))) cur = cur->next = new_hideset(h1->name);
    return head.next;
}

/// Adds an hideset to a token
static Token *add_hideset(Token *tok, Hideset *h) {
    Token head = {};
    Token *cur = &head;
    for (; tok; tok = tok->next) {
        Token *t = copy_token(tok);
        t->hideset = hideset_union(t->hideset, h);
        cur = cur->next = t;
    }
    return head.next;
}

/// Append a token to another token
static Token *append(Token *tok1, Token *tok2) {
    if (tok1->kind == TK_EOF) return tok2;
    Token head = {};
    Token *cur = &head;
    for (; tok1->kind != TK_EOF; tok1 = tok1->next) cur = cur->next = copy_token(tok1);
    cur->next = tok2;
    return head.next;
}

/// Skips a conditional inclusion until next `#else`, `#elif` or `#endif`
static Token *skip_cond_incl2(Token *tok) {
    while (tok->kind != TK_EOF) {
        if (is_hash(tok) &&
            (equal(tok->next, KW_IF) ||
             equal(tok->next, PP_IFDEF) ||
             equal(tok->next, PP_IFNDEF))) {
            tok = skip_cond_incl2(tok->next->next);
            continue;
        }
        if (is_hash(tok) && equal(tok->next, PP_ENDIF)) return tok->next->next;
        tok = tok->next;
    }
    return tok;
}

/// Skips a conditional inclusion until next `#else`, `#elif` or `#endif`
static Token *skip_cond_incl(Token *tok) {
    while (tok->kind != TK_EOF) {
        if (is_hash(tok) &&
            (equal(tok->next, KW_IF) ||
             equal(tok->next, PP_IFDEF) ||
             equal(tok->next, PP_IFNDEF))) {
            tok = skip_cond_incl2(tok->next->next);
            continue;
        }
        if (is_hash(tok) &&
            (equal(tok->next, PP_ELIF) ||
             equal(tok->next, KW_ELSE) ||
             equal(tok->next, PP_ENDIF)))
            break;
        tok = tok->next;
    }
    return tok;
}

/// Double-quote given string and return it
static char *quote_string(char *str) {
    int buf_size = 3;
    for (int i = 0; str[i]; i++) {
        if (str[i] == PT_BACKSLASH || str[i] == PT_QUOTE) buf_size++;
        buf_size++;
    }
    char *buf = calloc(1, buf_size);
    char *p = buf;
    *p++ = PT_QUOTE;
    for (int i = 0; str[i]; i++) {
        if (str[i] == PT_BACKSLASH || str[i] == PT_QUOTE) *p++ = PT_BACKSLASH;
        *p++ = str[i];
    }
    *p++ = PT_QUOTE;
    *p = ES_NUL;
    return buf;
}

/// Creates a new string token given a template and a value
static Token *new_str_token(char *str, Token *tmpl) {
    char *buf = quote_string(str);
    return tokenize(new_file(tmpl->file->name, tmpl->file->file_no, buf));
}

/// Copy all tokens 'til next newline, terminate them with an EOF token
/// and return. Used to create a new list of tokens for #if args.
static Token *copy_line(Token **rest, Token *tok) {
    Token head = {};
    Token  *cur = &head;
    for (; tok->kind != TK_EOF; tok = tok->next) cur = cur->next = copy_token(tok);
    cur->next = new_eof(tok);
    *rest = tok;
    return head.next;
}

/// Creates a new numeric token given a template and a value
static Token *new_num_token(int val, Token *tmpl) {
    char *buf = format("%d\n", val);
    return tokenize(new_file(tmpl->file->name, tmpl->file->file_no, buf));
}

/// Reads a constant expression defined as a macro
static Token *read_const_expr(Token **rest, Token *tok) {
    tok = copy_line(rest, tok);
    Token head = {};
    Token *cur = &head;
    while (tok->kind != TK_EOF) {
        /// `defined(some)` or `defined some` is translated to `1`if `some` is defined
        /// otherwise `0`.
        if (equal(tok, PP_DEFINED)) {
            Token *start = tok;
            bool has_paren = consume(&tok, tok->next, PT_PAREN_OPEN);
            if (tok->kind != TK_IDENT) error_tok(start, EXPECTED_ID_MACRO_NAME);
            Macro *m = find_macro(tok);
            tok = tok->next;
            if (has_paren) tok = skip(tok, PT_PAREN_CLOSE);
            cur = cur->next = new_num_token(m ? 1 : 0, start);
            continue;
        }
        cur = cur->next = tok;
        tok = tok->next;
    }
    cur->next = tok;
    return head.next;
}

/// Reads and evaluates constant expression
static long eval_const_expr(Token **rest, Token *tok) {
    Token *start = tok;
    Token *expr = read_const_expr(rest, tok->next);
    expr = preprocess2(expr);
    if (expr->kind == TK_EOF) error_tok(start, EXPECTED_CONST_EXPR);
    /// Standard wants that, if `#if some` is equivalent to `0`, it is considered as not-defined
    for (Token *t = expr; t->kind != TK_EOF; t = t->next) {
        if (t->kind == TK_IDENT) {
            Token *next = t->next;
            *t = *new_num_token(0, t);
            t->next = next;
        }
    }
    /// Convert preprocessed nums to nums
    convert_pp_tokens(expr);
    Token *rest2;
    long val = const_expr(&rest2, expr);
    if (rest2->kind != TK_EOF) error_tok(start, UNEXPECTED_TOKEN);
    return val;
}

/// Pushes a new conditional inclusion
static CondIncl *push_cond_incl(Token *tok, bool included) {
    CondIncl *ci = calloc(1, sizeof(CondIncl));
    ci->next = cond_incl;
    ci->ctx = IN_THEN;
    ci->tok = tok;
    ci->included = included;
    cond_incl = ci;
    return ci;
}

/// Finds a macro given a token
static Macro *find_macro(Token *tok) {
    if (tok->kind != TK_IDENT) return NULL;
    return hashmap_get_wlen(&macros, tok->loc, tok->len);
}

/// Adds a new macro given its characteristics
static Macro *add_macro(char *name, bool is_objlike, Token *body) {
    Macro *m = calloc(1, sizeof(Macro));
    m->name = name;
    m->is_objlike = is_objlike;
    m->body = body;
    hashmap_put(&macros, name, m);
    return m;
}

/// Reads macro parameters
static MacroParam *read_macro_params(Token **rest, Token *tok, char **va_args_name) {
    MacroParam head = {};
    MacroParam *cur = &head;
    while (!equal(tok, PT_PAREN_CLOSE)) {
        if (cur != &head) tok = skip(tok, PT_COMMA);
        if (equal(tok, PT_VARARGS))     {
            *va_args_name = PP_VARARGS;
            *rest = skip(tok->next, PT_PAREN_CLOSE);
            return head.next;
        }
        if (tok->kind != TK_IDENT) error_tok(tok, EXPECTED_ID_MACRO_NAME);
        if (equal(tok->next, PT_VARARGS)) {
            *va_args_name = strndup(tok->loc, tok->len);
            *rest = skip(tok->next->next, PT_PAREN_CLOSE);
            return head.next;
        }
        MacroParam *m = calloc(1, sizeof(MacroParam));
        m->name = strndup(tok->loc, tok->len);
        cur = cur->next = m;
        tok = tok->next;
    }
    *rest = tok->next;
    return head.next;
}

static void read_macro_definition(Token **rest, Token *tok) {
    if (tok->kind != TK_IDENT) error_tok(tok, EXPECTED_ID_MACRO_NAME);
    char *name = strndup(tok->loc, tok->len);
    tok = tok->next;
    if (!tok->has_space && equal(tok, PT_PAREN_OPEN)) {
        /// Function-like macro
        char *va_args_name = NULL;
        MacroParam *params = read_macro_params(&tok, tok->next, &va_args_name);
        Macro *m = add_macro(name, false, copy_line(rest, tok));
        m->params = params;
        m->va_args_name = va_args_name;
    } else {
        /// Object-like macro
        add_macro(name, true, copy_line(rest, tok));
    }
}

/// Reads a macro argument
static MacroArg *read_macro_arg_one(Token **rest, Token *tok, bool read_rest) {
    Token head = {};
    Token *cur = &head;
    int level = 0;
    for (;;) {
        if (level == 0 && equal(tok, PT_PAREN_CLOSE)) break;
        if (level == 0 && !read_rest && equal(tok, PT_COMMA)) break;
        if (tok->kind == TK_EOF) error_tok(tok, UNT_MACRO_ARG);
        if (equal(tok, PT_PAREN_OPEN)) level++;
        else if (equal(tok, PT_PAREN_CLOSE)) level--;
        cur = cur->next = copy_token(tok);
        tok = tok->next;
    }
    cur->next = new_eof(tok);
    MacroArg *arg = calloc(1, sizeof(MacroArg));
    arg->tok = head.next;
    *rest = tok;
    return arg;
}

/// Reads macro arguments
static MacroArg *read_macro_args(Token **rest, Token *tok, MacroParam *params, char *va_args_name) {
    Token *start = tok;
    tok = tok->next->next;
    MacroArg head = {};
    MacroArg *cur = &head;
    MacroParam *pp = params;
    for (; pp; pp = pp->next) {
        if (cur != &head)  tok = skip(tok, PT_COMMA);
        cur = cur->next = read_macro_arg_one(&tok, tok, false);
        cur->name = pp->name;
    }
    if (va_args_name) {
        MacroArg *arg;
        if (equal(tok, PT_PAREN_CLOSE)) {
            arg = calloc(1, sizeof(MacroArg));
            arg->tok = new_eof(tok);
        } else {
            if (pp != params) tok = skip(tok, PT_COMMA);
            arg = read_macro_arg_one(&tok, tok, true);
        }
        arg->name = va_args_name;;
        bool is_va_args = true;
        arg->is_va_args = &is_va_args;
        cur = cur->next = arg;
    } else if (pp) {
        error_tok(start, TOO_MANY_ARGS);
    }
    skip(tok, PT_PAREN_CLOSE);
    *rest = tok;
    return head.next;
}

/// Finds an arg in a list of args
static MacroArg *find_arg(MacroArg *args, Token *tok) {
    for (MacroArg *ap = args; ap; ap = ap->next) {
        if (tok->len == strlen(ap->name) && !strncmp(tok->loc, ap->name, tok->len)) return ap;
        return NULL;
    }
}

/// Concatenates all tokens in `tok` until `end`, returns then a new string.
static char *join_tokens(Token *tok, Token *end) {
    int len = 1;
    for (Token *t = tok; t != end && t->kind != TK_EOF; t = t->next) {
        if (t != tok && t->has_space) len++;
        len += t->len;
    }
    char *buf = calloc(1, len);
    int pos = 0;
    for (Token *t = tok; t != end && t->kind != TK_EOF; t = t->next) {
        if (t != tok && t->has_space) buf[pos++] = ' ';
        strncpy(buf + pos, t->loc, t->len);
        pos += t->len;
    }
    buf[pos] = ES_NUL;
    return buf;
}

/// Concat all tokens in `arg` and return new string token
/// Used for stringizing operator `#`.
static Token *stringize(Token *hash, Token *arg){
    char *s = join_tokens(arg, NULL);
    return new_str_token(s, hash);
}

/// Concat two tokens to create a new one
static Token *paste(Token *lhs, Token *rhs) {
    char *buf = format("%.*s%.*s", lhs->len, lhs->loc, rhs->len, rhs->loc);
    Token *tok = tokenize(new_file(lhs->file->name, lhs->file->file_no, buf));
    if (tok->next->kind != TK_EOF) error_tok(lhs, INV_TOKEN_PASTE, buf);
    return tok;
}

/// Check if `args` has `__VA_ARGS__`
static bool has_varargs(MacroArg *args) {
    for (MacroArg *ap = args; ap; ap = ap->next) {
        if (!strcmp(ap->name, PP_VARARGS)) return ap->tok->kind != TK_EOF;
        return false;
    }
}

/// Replace func-like macro parameters with given arguments.
static Token *subst(Token *tok, MacroArg *args) {
    Token head = {};
    Token *cur = &head;
    while (tok->kind != TK_EOF) {
        if (equal(tok, PP_POUND)) {
            MacroArg *arg = find_arg(args, tok->next);
            if (!arg) error_tok(tok->next, MISSING_MACRO_PARAM);
            cur = cur->next = stringize(tok, arg->tok);
            tok = tok->next->next;
            continue;
        }
        /// [GNU] If __VA_ARG__ is empty, `,##__VA_ARGS__` is expanded
        /// to the empty token list. Otherwise, its expaned to `,` and
        /// __VA_ARGS__.
        if (equal(tok, PT_COMMA) && equal(tok->next, PP_POUND_POUND)) {
            MacroArg *arg = find_arg(args, tok->next->next);
            if (arg && arg->is_va_args) {
                if (arg->tok->kind == TK_EOF) tok = tok->next->next->next;
                else {
                    cur = cur->next = copy_token(tok);
                    tok = tok->next->next;
                }
                continue;
            }
        }
        if (equal(tok, PP_POUND_POUND)) {
            if (cur == &head) error_tok(tok, UNEXPECTED_DPOUND_SOE);
            if (tok->next->kind == TK_EOF) error_tok(tok, UNEXPECTED_DPOUND_EOE);
            MacroArg *arg = find_arg(args, tok->next);
            if (arg) {
                if (arg->tok->kind != TK_EOF) {
                    *cur = *paste(cur, arg->tok);
                    for (Token *t = arg->tok->next; t->kind != TK_EOF; t = t->next) cur = cur->next = copy_token(t);
                }
                tok = tok->next->next;
                continue;
            }
            *cur = *paste(cur, tok->next);
            tok = tok->next->next;
            continue;
        }
        MacroArg *arg = find_arg(args, tok);
        if (arg && equal(tok->next, PP_POUND_POUND)) {
            Token *rhs = tok->next->next;
            if (arg->tok->kind == TK_EOF) {
                MacroArg *arg2 = find_arg(args, rhs);
                if (arg2) {
                    for (Token *t = arg2->tok; t->kind != TK_EOF; t = t->next) cur = cur->next = copy_token(t);
                } else {
                    cur = cur->next = copy_token(rhs);
                }
                tok = rhs->next;
                continue;
            }
            for (Token *t = arg->tok; t->kind != TK_EOF; t = t->next) cur = cur->next = copy_token(t);
            tok = tok->next;
            continue;
        }
        /// If __VA_ARG__ is empty, __VA_OPT__(x) is expanded to the
        /// empty token list. Otherwise, __VA_OPT__(x) is expanded to x.
        if (equal(tok, "__VA_OPT__") && equal(tok->next, PT_PAREN_OPEN)) {
            MacroArg *arg = read_macro_arg_one(&tok, tok->next->next, true);
            if (has_varargs(args))
                for (Token *t = arg->tok; t->kind != TK_EOF; t = t->next) cur = cur->next = t;
            tok = skip(tok, PT_PAREN_CLOSE);
            continue;
        }
        /// Handle a macro token. Macro arguments are completely macro-expanded
        /// before they are substituted into a macro body.
        if (arg) {
            Token *t = preprocess2(arg->tok);
            t->at_sol = tok->at_sol;
            t->has_space = tok->has_space;
            for (; t->kind != TK_EOF; t = t->next) cur = cur->next = copy_token(t);
            tok = tok->next;
            continue;
        }
        /// Handle a non-macro token.
        cur = cur->next = copy_token(tok);
        tok = tok->next;
    }
    cur->next = tok;
    return head.next;
}

/// If tok is macro, expand it and return true. Otherwise, return false.
static bool expand_macro(Token **rest, Token *tok) {
    if (hideset_contains(tok->hideset, tok->loc, tok->len)) return false;
    Macro *m = find_macro(tok);
    if (!m) return false;
    /// Builtin dyn macro
    if (m->handler) {
        *rest = m->handler(tok);
        (*rest)->next = tok->next;
        return true;
    }
    /// Obj-like macro app
    if (m->is_objlike) {
        Hideset *hs = hideset_union(tok->hideset, new_hideset(m->name));
        Token *body = add_hideset(m->body, hs);
        for (Token *t = body; t->kind != TK_EOF; t = t->next) t->origin = tok;
        *rest = append(body, tok->next);
        (*rest)->at_sol = tok->at_sol;
        (*rest)->has_space = tok->has_space;
        return true;
    }
    /// If fn-like macro tok is not followed by arg list
    /// treat as normal identifier.
    if (!equal(tok->next, PT_PAREN_OPEN)) return false;
    /// Fn-line macro app
    Token *macro_token = tok;
    MacroArg *args = read_macro_args(&tok, tok, m->params, m->va_args_name);
    Token *rparen = tok;
    /// Token of a fn-like macro invocation can have different hidesets.
    /// In that case hideset is not definable. As the Dave Prossor's algorithm defines
    /// hideset can be determined by the intersection of macro tok and closing parentheses.
    Hideset *hs = hideset_intersection(macro_token->hideset, rparen->hideset);
    hs = hideset_union(hs, new_hideset(m->name));
    Token *body = subst(m->body, args);
    body = add_hideset(body, hs);
    for (Token *t = body; t->kind != TK_EOF; t = t->next) t->origin = macro_token;
    *rest = append(body, tok->next);
    (*rest)->at_sol = macro_token->at_sol;
    (*rest)->has_space = macro_token->has_space;
    return true;
}

/// Search include paths
char *search_include_paths(char *filename) {
    if (filename[0] == '/') return filename;
    static HashMap cache;
    char *cached = hashmap_get(&cache, filename);
    if (cached) return cached;
    for (int i = 0; i < include_paths.len; i++) {
        char *path = format("%s/%s", include_paths.data[i], filename);
        if (!file_exists(path)) continue;
        hashmap_put(&cache, filename, path);
        include_next_idx = i + 1;
        return path;
    }
    return NULL;
}

/// Search include next
static char *search_include_next(char *filename) {
    for (; include_next_idx < include_paths.len; include_next_idx++) {
        char *path = format("%s/%s", include_paths.data[include_next_idx], filename);
        if (file_exists(path)) return path;
    }
    return NULL;
}

/// Read #include filename macros
static char *read_include_filename(Token **rest, Token *tok, bool *is_dquote) {
    /// Pattern: `#include "filename.h"`
    if (tok->kind == TK_STR) {
        /// A double-quoted filename for #include is a special kind of
        /// token, and we don't want to interpret any escape sequences in it.
        /// For example, "\f" in "C:\foo" is not a formfeed character but
        /// just two non-control characters, backslash and f.
        /// So we don't want to use token->str.
        *is_dquote = true;
        *rest = skip_line(tok->next);
        return strndup(tok->loc + 1, tok->len - 2);
    }
    /// Pattern: `#include <filename.h>`
    if (equal(tok, OP_LOG_LT)) {
        /// Reconstructs filename from sequence of tokens between `<` and `>`
        Token *start = tok;
        /// Find closing angular bracket
        for (; !equal(tok, OP_LOG_GT); tok = tok->next)
            if (tok->kind == TK_EOF) error_tok(tok, UNT_INCLUDE);
        *is_dquote = false;
        *rest = skip_line(tok->next);
        return join_tokens(start->next, tok);
    }
    /// Pattern: `#include FILENAME`
    /// This case foresees that the filename must be macro-expanded
    /// to single str or enclosed in angular brackets
    if (tok->kind == TK_IDENT) {
        Token *tok2 = preprocess2(copy_line(rest, tok));
        return read_include_filename(&tok2, tok2, is_dquote);
    }
    error_tok(tok, MISSING_FILENAME);
}

/// Detect include guard pattern:
/// ```c
/// #ifndef FILENAME
/// #define FILENAME
/// ...
/// #endif
/// ```
static char *detect_include_guard(Token *tok) {
    /// Detect the first 2 lines
    if (!is_hash(tok) || !equal(tok->next, PP_IFNDEF)) return NULL;
    tok = tok->next->next;
    if (tok->kind != TK_IDENT) return NULL;
    char *macro = strndup(tok->loc, tok->len);
    tok = tok->next;
    if (!is_hash(tok) || !equal(tok->next, PP_DEFINE) || !equal(tok->next->next, macro)) return NULL;
    while (tok->kind != TK_EOF) {
        if (!is_hash(tok)) {
            tok = tok->next;
            continue;
        }
        if (equal(tok->next, PP_ENDIF) && tok->next->next->kind == TK_EOF) return macro;
        if (equal(tok, KW_IF) || equal(tok, PP_IFDEF) || equal(tok, PP_IFNDEF))
            tok = skip_cond_incl(tok->next);
        else tok = tok->next;
    }
    return NULL;
}

/// Read include file macros
static Token *include_file(Token *tok, char *path, Token *filename_tok) {
    /// Check for "#pragma once"
    if (hashmap_get(&pragma_once, path)) return tok;
    /// If we read the same file before, and if the file was guarded
    /// by the usual #ifndef ... #endif pattern, we may be able to
    /// skip the file without opening it.
    static HashMap include_guards;
    char *guard_name = hashmap_get(&include_guards, path);
    if (guard_name && hashmap_get(&macros, guard_name)) return tok;
    Token *tok2 = tokenize_file(path);
    if (!tok2) error_tok(filename_tok, CANNOT_OPEN_FILE, path, strerror(errno));
    guard_name = detect_include_guard(tok2);
    if (guard_name) hashmap_put(&include_guards, path, guard_name);
    return append(tok2, tok);
}

/// Read #line arguments
static void read_line_marker(Token **rest, Token *tok) {
    Token *start = tok;
    tok = preprocess(copy_line(rest, tok));
    if (tok->kind != TK_NUM || tok->ty->kind != TY_INT) error_tok(tok, INV_LINE_MARK);
    start->file->line_delta = tok->val - start->line_no;
    tok = tok->next;
    if (tok->kind == TK_EOF) return;
    if (tok->kind != TK_STR) error_tok(tok, MISSING_FILENAME);
    start->file->display_name = tok->str;
}

/// Go to all tokens in `tok` while eval preproc
/// macros and directives.
static Token *preprocess2(Token *tok) {
    Token head = {};
    Token *cur = &head;
    while (tok->kind != TK_EOF) {
        /// If it is a macro, expand it.
        if (expand_macro(&tok, tok)) continue;
        /// Pass through if it is not a PP_POUND.
        if (!is_hash(tok)) {
            tok->line_delta = tok->file->line_delta;
            tok->filename = tok->file->display_name;
            cur = cur->next = tok;
            tok = tok->next;
            continue;
        }
        Token *start = tok;
        tok = tok->next;
        if (equal(tok, PP_INCLUDE)) {
            bool is_dquote;
            char *filename = read_include_filename(&tok, tok->next, &is_dquote);
            if (filename[0] != '/' && is_dquote) {
                char *path = format("%s/%s", dirname(strdup(start->file->name)), filename);
                if (file_exists(path)) {
                    tok = include_file(tok, path, start->next->next);
                    continue;
                }
            }
            char *path = search_include_paths(filename);
            tok = include_file(tok, path ? path : filename, start->next->next);
            continue;
        }
        if (equal(tok, PP_INCLUDE_NEXT)) {
            bool ignore;
            char *filename = read_include_filename(&tok, tok->next, &ignore);
            char *path = search_include_next(filename);
            tok = include_file(tok, path ? path : filename, start->next->next);
            continue;
        }
        if (equal(tok, PP_DEFINE)) {
            read_macro_definition(&tok, tok->next);
            continue;
        }
        if (equal(tok, PP_UNDEF)) {
            tok = tok->next;
            if (tok->kind != TK_IDENT) error_tok(tok, EXPECTED_ID_MACRO_NAME);
            undefine_macro(strndup(tok->loc, tok->len));
            tok = skip_line(tok->next);
            continue;
        }
        if (equal(tok, KW_IF)) {
            long val = eval_const_expr(&tok, tok);
            push_cond_incl(start, val);
            if (!val) tok = skip_cond_incl(tok);
            continue;
        }
        if (equal(tok, PP_IFDEF)) {
            bool defined = find_macro(tok->next);
            push_cond_incl(tok, defined);
            tok = skip_line(tok->next->next);
            if (!defined) tok = skip_cond_incl(tok);
            continue;
        }
        if (equal(tok, PP_IFNDEF)) {
            bool defined = find_macro(tok->next);
            push_cond_incl(tok, !defined);
            tok = skip_line(tok->next->next);
            if (defined) tok = skip_cond_incl(tok);
            continue;
        }
        if (equal(tok, PP_ELIF)) {
            if (!cond_incl || cond_incl->ctx == IN_ELSE) error_tok(start, STRAY_PP_TOKEN, PP_ELIF);
            cond_incl->ctx = IN_ELIF;
            if (!cond_incl->included && eval_const_expr(&tok, tok)) cond_incl->included = true;
            else tok = skip_cond_incl(tok);
            continue;
        }
        if (equal(tok, KW_ELSE)) {
            if (!cond_incl || cond_incl->ctx == IN_ELSE) error_tok(start, STRAY_PP_TOKEN, KW_ELSE);
            cond_incl->ctx = IN_ELSE;
            tok = skip_line(tok->next);
            if (cond_incl->included) tok = skip_cond_incl(tok);
            continue;
        }
        if (equal(tok, PP_ENDIF)) {
            if (!cond_incl) error_tok(start, STRAY_PP_TOKEN, PP_ENDIF);
            cond_incl = cond_incl->next;
            tok = skip_line(tok->next);
            continue;
        }
        if (equal(tok, PP_LINE)) {
            read_line_marker(&tok, tok->next);
            continue;
        }
        if (tok->kind == TK_PP_NUM) {
            read_line_marker(&tok, tok);
            continue;
        }
        if (equal(tok, PP_PRAGMA) && equal(tok->next, "once")) {
            hashmap_put(&pragma_once, tok->file->name, (void *)1);
            tok = skip_line(tok->next->next);
            continue;
        }
        if (equal(tok, PP_PRAGMA)) {
            do {
                tok = tok->next;
            } while (!tok->at_sol);
            continue;
        }
        if (equal(tok, PP_ERROR)) error_tok(tok, PP_ERROR);
        /// `#`-only line is legal. It's called a null directive.
        if (tok->at_sol) continue;
        error_tok(tok, INV_PP_DIR);
    }
    cur->next = tok;
    return head.next;
}

/// Define built-in macros
void define_macro(char *name, char *buf) {
    Token *tok = tokenize(new_file("<built-in>", 1, buf));
    add_macro(name, true, tok);
}

/// Undefine built-in macros
void undefine_macro(char *name) {
    hashmap_delete(&macros, name);
}

/// Add a built-in macro
static Macro *add_builtin(char *name, macro_handler_fn *fn) {
    Macro *m = add_macro(name, true, NULL);
    m->handler = fn;
    return m;
}

/// __FILE__ is expanded to the current file name
static Token *file_macro(Token *tmpl) {
    while (tmpl->origin) tmpl = tmpl->origin;
    return new_str_token(tmpl->file->display_name, tmpl);
}

/// __LINE__ is expanded to the current line number
static Token *line_macro(Token *tmpl) {
    while (tmpl->origin) tmpl = tmpl->origin;
    int i = tmpl->line_no + tmpl->file->line_delta;
    return new_num_token(i, tmpl);
}

/// __COUNTER__ is expanded to serial values starting from 0.
static Token *counter_macro(Token *tmpl) {
    static int i = 0;
    return new_num_token(i++, tmpl);
}

/// __TIMESTAMP__ is expanded to a string describing the last
/// modification time of the current file. E.g.
/// "Sun Feb 4 14:29:32 2024"
static Token *timestamp_macro(Token *tmpl) {
    struct stat st;
    if (stat(tmpl->file->name, &st) != 0) return new_str_token("??? ??? ?? ??:??:?? ????", tmpl);
    char buf[30];
    ctime_r(&st.st_mtime, buf);
    buf[24] = ES_NUL;
    return new_str_token(buf, tmpl);
}

/// __BASE_FILE__ is expanded to the base name of the current file
static Token *base_file_macro(Token *tmpl) {
    return new_str_token(base_file, tmpl);
}

/// __DATE__ is expanded to the current date, e.g. "May 17 2020".
static char *format_date(struct tm *tm) {
    static char mon[][4] = {
            "Jan", "Feb", "Mar", "Apr", "May", "Jun",
            "Jul", "Aug", "Sep", "Oct", "Nov", "Dec",
    };
    return format("\"%s %2d %d\"", mon[tm->tm_mon], tm->tm_mday, tm->tm_year + 1900);
}

/// __TIME__ is expanded to the current time, e.g. "14:30:21".
static char *format_time(struct tm *tm) {
    return format("\"%02d:%02d:%02d\"", tm->tm_hour, tm->tm_min, tm->tm_sec);
}

/// Initialize predefined macros
/// TODO: DEFINE ACE BUILTIN MACROS
void init_macros(void) {
    // Define predefined macros
    define_macro("_LP64", "1");
    define_macro("__C99_MACRO_WITH_VA_ARGS", "1");
    define_macro("__ELF__", "1");
    define_macro("__LP64__", "1");
    define_macro("__SIZEOF_DOUBLE__", "8");
    define_macro("__SIZEOF_FLOAT__", "4");
    define_macro("__SIZEOF_INT__", "4");
    define_macro("__SIZEOF_LONG_DOUBLE__", "8");
    define_macro("__SIZEOF_LONG_LONG__", "8");
    define_macro("__SIZEOF_LONG__", "8");
    define_macro("__SIZEOF_POINTER__", "8");
    define_macro("__SIZEOF_PTRDIFF_T__", "8");
    define_macro("__SIZEOF_SHORT__", "2");
    define_macro("__SIZEOF_SIZE_T__", "8");
    define_macro("__SIZE_TYPE__", "unsigned long");
    define_macro("__STDC_HOSTED__", "1");
    define_macro("__STDC_NO_COMPLEX__", "1");
    define_macro("__STDC_UTF_16__", "1");
    define_macro("__STDC_UTF_32__", "1");
    define_macro("__STDC_VERSION__", "201112L");
    define_macro("__STDC__", "1");
    define_macro("__USER_LABEL_PREFIX__", "");
    define_macro("__alignof__", "_Alignof");
    define_macro("__amd64", "1");
    define_macro("__amd64__", "1");
    define_macro("__chibicc__", "1");
    define_macro("__const__", "const");
    define_macro("__gnu_linux__", "1");
    define_macro("__inline__", "inline");
    define_macro("__linux", "1");
    define_macro("__linux__", "1");
    define_macro("__signed__", "signed");
    define_macro("__typeof__", "typeof");
    define_macro("__unix", "1");
    define_macro("__unix__", "1");
    define_macro("__volatile__", "volatile");
    define_macro("__x86_64", "1");
    define_macro("__x86_64__", "1");
    define_macro("linux", "1");
    define_macro("unix", "1");
    add_builtin("__FILE__", file_macro);
    add_builtin("__LINE__", line_macro);
    add_builtin("__COUNTER__", counter_macro);
    add_builtin("__TIMESTAMP__", timestamp_macro);
    add_builtin("__BASE_FILE__", base_file_macro);
    time_t now = time(NULL);
    struct tm *tm = localtime(&now);
    define_macro("__DATE__", format_date(tm));
    define_macro("__TIME__", format_time(tm));
}

/// Type definition for a string
typedef enum {
    STR_NONE, STR_UTF8, STR_UTF16, STR_UTF32, STR_WIDE,
} StringKind;

/// Get string kind
static StringKind get_string_kind(Token *tok) {
    if (!strcmp(tok->loc, "u8")) return STR_UTF8;
    switch (tok->loc[0]) {
        case PT_QUOTE: return STR_NONE;
        case 'u': return STR_UTF16;
        case 'U': return STR_UTF32;
        case 'L': return STR_WIDE;
    }
    unreachable();
}

/// Concat adj string literals into single string literal
static void join_adjacent_string_literals(Token *tok) {
    /// If reg string literals are adj to wide
    /// string literals, reg string literals are converted to a wide
    /// type before concatenation
    for (Token *tok1 = tok; tok1->kind != TK_EOF;) {
        if (tok1->kind != TK_STR || tok1->next->kind != TK_STR) {
            tok1 = tok1->next;
            continue;
        }
        StringKind kind = get_string_kind(tok1);
        Type *basety = tok1->ty->base;
        for (Token *t = tok1->next; t->kind == TK_STR; t = t->next) {
            StringKind k = get_string_kind(t);
            if (kind == STR_NONE) {
                kind = k;
                basety = t->ty->base;
            } else if (k != STR_NONE && kind != k) {
                error_tok(t, NSTD_CONCAT);
            }
        }
        if (basety->size > 1)
            for (Token *t = tok1; t->kind == TK_STR; t = t->next)
                if (t->ty->base->size == 1) *t = *tokenize_string_literal(t, basety);
        while (tok1->kind == TK_STR) tok1 = tok1->next;
    }
    /// Concatenate adjacent string literals.
    for (Token *tok1 = tok; tok1->kind != TK_EOF;) {
        if (tok1->kind != TK_STR || tok1->next->kind != TK_STR) {
            tok1 = tok1->next;
            continue;
        }
        Token *tok2 = tok1->next;
        while (tok2->kind == TK_STR) tok2 = tok2->next;
        int len = tok1->ty->array_len;
        for (Token *t = tok1->next; t != tok2; t = t->next) len = len + t->ty->array_len - 1;
        char *buf = calloc(tok1->ty->base->size, len);
        int i = 0;
        for (Token *t = tok1; t != tok2; t = t->next) {
            memcpy(buf + i, t->str, t->ty->size);
            i = i + t->ty->size - t->ty->base->size;
        }
        *tok1 = *copy_token(tok1);
        tok1->ty = array_of(tok1->ty->base, len);
        tok1->str = buf;
        tok1->next = tok2;
        tok1 = tok2;
    }
}

/// Entry point function of the preprocessor.
Token *preprocess(Token *tok) {
    tok = preprocess2(tok);
    if (cond_incl) error_tok(cond_incl->tok, UNT_COND_DIR);
    convert_pp_tokens(tok);
    join_adjacent_string_literals(tok);
    for (Token *t = tok; t; t = t->next) t->line_no += t->line_delta;
    return tok;
}
