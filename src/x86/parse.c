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
// Created by Luca Mazza on 2024/2/4.
// TODO: adapt to ace

#include "acec.h"
#include "../../definitions/syntax.h"
#include "../../definitions/errmsg.h"

/// Local, global variables and typedefs or enum constants type definition
typedef struct {
    Obj *var;
    Type *type_def;
    Type *enum_ty;
    int enum_val;
} VarScope;

/// Block scope type definition
typedef struct Scope Scope;

/// Variable attributes type definition
typedef struct {
    bool is_typedef;
    bool is_static;
    bool is_extern;
    bool is_inline;
    bool is_tls;
    int align;
} VarAttr;

/// This struct represents a variable initializer. Since initializers
/// can be nested (e.g. `int x[2][2] = {{1, 2}, {3, 4}}`), this struct
/// is a tree data structure.
typedef struct Initializer Initializer;

/// Local variable initializer type definition
typedef struct InitDesg InitDesg;

/// Block scope structure
struct Scope {
    Scope *next;
    HashMap vars;
    HashMap tags;
};

/// Initializer structure
struct Initializer {
    Initializer *next;
    Type *ty;
    Token *tok;
    bool is_flexible;
    /// If it's not an aggregate type and has an initializer,
    /// `expr` has an initialization expression.
    Node *expr;
    /// If it's an initializer for an aggregate type (e.g. array or struct),
    /// `children` has initializers for its children.
    Initializer **children;
    /// Only one member can be initialized for a union.
    /// `mem` is used to clarify which member is initialized.
    Member *mem;
};

struct InitDesg {
    InitDesg *next;
    int idx;
    Member *member;
    Obj *var;
};

/// All local variable instances created during parsing are
/// accumulated to this list.
static Obj *locals;

/// Likewise, global variables are accumulated to this list.
static Obj *globals;
static Scope *scope = &(Scope){};

/// Points to the function object the parser is currently parsing.
static Obj *current_fn;

/// Lists of all goto statements and labels in the curent function.
static Node *gotos;
static Node *labels;

/// Current "goto" and "continue" jump targets.
static char *brk_label;
static char *cont_label;

/// Points to a node representing a switch if we are parsing
/// a switch statement. Otherwise, NULL.
static Node *current_switch;
static Obj *builtin_alloca;

static bool is_typename(Token *tok);

static Type *declspec(Token **rest, Token *tok, VarAttr *attr);

static Type *typename(Token **rest, Token *tok);

static Type *enum_specifier(Token **rest, Token *tok);

static Type *typeof_specifier(Token **rest, Token *tok);

static Type *type_suffix(Token **rest, Token *tok, Type *ty);

static Type *declarator(Token **rest, Token *tok, Type *ty);

static Node *declaration(Token **rest, Token *tok, Type *basety, VarAttr *attr);

static void array_initializer2(Token **rest, Token *tok, Initializer *init, int i);

static void struct_initializer2(Token **rest, Token *tok, Initializer *init, Member *mem);

static void initializer2(Token **rest, Token *tok, Initializer *init);

static Initializer *initializer(Token **rest, Token *tok, Type *ty, Type **new_ty);

static Node *lvar_initializer(Token **rest, Token *tok, Obj *var);

static void gvar_initializer(Token **rest, Token *tok, Obj *var);

static Node *compound_stmt(Token **rest, Token *tok);

static Node *stmt(Token **rest, Token *tok);

static Node *expr_stmt(Token **rest, Token *tok);

static Node *expr(Token **rest, Token *tok);

static int64_t eval(Node *node);

static int64_t eval2(Node *node, char ***label);

static int64_t eval_rval(Node *node, char ***label);

static bool is_const_expr(Node *node);

static Node *assign(Token **rest, Token *tok);

static Node *logor(Token **rest, Token *tok);

static double eval_double(Node *node);

static Node *conditional(Token **rest, Token *tok);

static Node *logand(Token **rest, Token *tok);

static Node *bitor(Token **rest, Token *tok);

static Node *bitxor(Token **rest, Token *tok);

static Node *bitand(Token **rest, Token *tok);

static Node *equality(Token **rest, Token *tok);

static Node *relational(Token **rest, Token *tok);

static Node *shift(Token **rest, Token *tok);

static Node *add(Token **rest, Token *tok);

static Node *new_add(Node *lhs, Node *rhs, Token *tok);

static Node *new_sub(Node *lhs, Node *rhs, Token *tok);

static Node *mul(Token **rest, Token *tok);

static Node *cast(Token **rest, Token *tok);

static Member *get_struct_member(Type *ty, Token *tok);

static Type *struct_decl(Token **rest, Token *tok);

static Type *union_decl(Token **rest, Token *tok);

static Node *postfix(Token **rest, Token *tok);

static Node *funcall(Token **rest, Token *tok, Node *node);

static Node *unary(Token **rest, Token *tok);

static Node *primary(Token **rest, Token *tok);

static Token *parse_typedef(Token *tok, Type *basety);

static bool is_function(Token *tok);

static Token *function(Token *tok, Type *basety, VarAttr *attr);

static Token *global_variable(Token *tok, Type *basety, VarAttr *attr);

/// Aligns down to the nearest multiple of `align`.
static int align_down(int n, int align) {
    return align_to(n - align + 1, align);
}

/// Enters a new scope.
static void enter_scope(void) {
    Scope *sc = calloc(1, sizeof(Scope));
    sc->next = scope;
    scope = sc;
}

/// Exits the current scope.
static void leave_scope(void) {
    scope = scope->next;
}

/// Find var by name
static VarScope *find_var(Token *tok) {
    for (Scope *sc = scope; sc; sc = sc->next) {
        VarScope *sc2 = hashmap_get_wlen(&sc->vars, tok->loc, tok->len);
        if (sc2) return sc2;
    }
    return NULL;
}

/// Finds a tag given its name
static Type *find_tag(Token *tok) {
    for (Scope *sc = scope; sc; sc = sc->next) {
        Type *ty = hashmap_get_wlen(&sc->tags, tok->loc, tok->len);
        if (ty) return ty;
    }
    return NULL;
}

/// Creates a new node
static Node *new_node(NodeKind kind, Token *tok) {
    Node *node = calloc(1, sizeof(Node));
    node->kind = kind;
    node->tok = tok;
    return node;
}

/// Creates a new binary node
static Node *new_binary(NodeKind kind, Node *lhs, Node *rhs, Token *tok) {
    Node *node = new_node(kind, tok);
    node->lhs = lhs;
    node->rhs = rhs;
    return node;
}

/// Creates a new unary node
static Node *new_unary(NodeKind kind, Node *expr, Token *tok) {
    Node *node = new_node(kind, tok);
    node->lhs = expr;
    return node;
}

/// Creates a new number node
static Node *new_num(int64_t val, Token *tok) {
    Node *node = new_node(ND_NUM, tok);
    node->val = val;
    return node;
}

/// Creates a new long number node
static Node *new_long(int64_t val, Token *tok) {
    Node *node = new_node(ND_NUM, tok);
    node->val = val;
    node->ty = ty_long;
    return node;
}

/// Creates a new unsigned long number node
static Node *new_ulong(long val, Token *tok) {
    Node *node = new_node(ND_NUM, tok);
    node->val = val;
    node->ty = ty_ulong;
    return node;
}

/// Creates a new variable node
static Node *new_var_node(Obj *var, Token *tok) {
    Node *node = new_node(ND_VAR, tok);
    node->var = var;
    return node;
}

/// Creates a new VLA pointer node
static Node *new_vla_ptr(Type *ty, Token *tok) {
    Node *node = new_node(ND_VLA_PTR, tok);
    node->ty = ty;
    return node;
}

/// Creates a new cast node
Node *new_cast(Node *expr, Type *ty) {
    add_type(expr);
    Node *node = calloc(1, sizeof(Node));
    node->kind = ND_CAST;
    node->tok = expr->tok;
    node->lhs = expr;
    node->ty = copy_type(ty);
    return node;
}

/// Push a new scope
static VarScope *push_scope(char *name) {
    VarScope *sc = calloc(1, sizeof(VarScope));
    hashmap_put(&scope->vars, name, sc);
    return sc;
}

/// Creates a new initializer
static Initializer *new_initializer(Type *ty, bool is_flexible) {
    Initializer *init = calloc(1, sizeof(Initializer));
    init->ty = ty;
    if (ty->kind == TY_ARRAY) {
        if (is_flexible && ty->size < 0) {
            init->is_flexible = true;
            return init;
        }
        init->children = calloc(ty->array_len, sizeof(Initializer *));
        for (int i = 0; i < ty->array_len; i++) init->children[i] = new_initializer(ty->base, false);
        return init;
    }
    if (ty->kind == TY_STRUCT || ty->kind == TY_UNION) {
        int len = 0;
        for (Member *mem = ty->members; mem; mem = mem->next) len++;
        init->children = calloc(len, sizeof(Initializer *));
        for (Member *mem = ty->members; mem; mem = mem->next) {
            if (is_flexible && ty->is_flexible && !mem->next) {
                Initializer *child = calloc(1, sizeof(Initializer));
                child->ty = mem->ty;
                child->is_flexible = true;
                init->children[mem->idx] = child;
            } else {
                init->children[mem->idx] = new_initializer(mem->ty, false);
            }
        }
        return init;
    }
    return init;
}

/// Creates a new variable
static Obj *new_var(char *name, Type *ty) {
    Obj *var = calloc(1, sizeof(Obj));
    var->name = name;
    var->ty = ty;
    var->align = ty->align;
    push_scope(name)->var = var;
    return var;
}

/// Creates a new local variable
static Obj *new_lvar(char *name, Type *ty) {
    Obj *var = new_var(name, ty);
    var->is_local = true;
    var->next = locals;
    locals = var;
    return var;
}

/// Creates a new global variable
static Obj *new_gvar(char *name, Type *ty) {
    Obj *var = new_var(name, ty);
    var->next = globals;
    var->is_static = true;
    var->is_definition = true;
    globals = var;
    return var;
}

/// Creates a new unique name
static char *new_unique_name(void) {
    static int id = 0;
    return format(".L..%d", id++);
}

/// Creates a new anonymous global variable
static Obj *new_anon_gvar(Type *ty) {
    return new_gvar(new_unique_name(), ty);
}

/// Creates a new string literal
static Obj *new_string_literal(char *p, Type *ty) {
    Obj *var = new_anon_gvar(ty);
    var->init_data = p;
    return var;
}

/// Gets an identifier
static char *get_ident(Token *tok) {
    if (tok->kind != TK_IDENT) error_tok(tok, EXPECTED_ID);
    return strndup(tok->loc, tok->len);
}

/// Finds a type definition
static Type *find_typedef(Token *tok) {
    if (tok->kind == TK_IDENT) {
        VarScope *sc = find_var(tok);
        if (sc) return sc->type_def;
    }
    return NULL;
}

/// Push a new tag scope
static void push_tag_scope(Token *tok, Type *ty) {
    hashmap_put_wlen(&scope->tags, tok->loc, tok->len, ty);
}

/// In this function, we count the number of occurrences of each typename
/// while keeping the "current" type object that the typenames up
/// until that point represent. When we reach a non-typename token,
/// we returns the current type object.
static Type *declspec(Token **rest, Token *tok, VarAttr *attr) {
    // We use a single integer as counters for all typenames.
    // For example, bits 0 and 1 represents how many times we saw the
    // keyword "void" so far.
    enum {
        VOID     = 1 << 0,
        BOOL     = 1 << 2,
        CHAR     = 1 << 4,
        SHORT    = 1 << 6,
        INT      = 1 << 8,
        LONG     = 1 << 10,
        FLOAT    = 1 << 12,
        DOUBLE   = 1 << 14,
        OTHER    = 1 << 16,
        SIGNED   = 1 << 17,
        UNSIGNED = 1 << 20
    };
    Type *ty = ty_int;
    int counter = 0;
    bool is_atomic = false;
    while (is_typename(tok)) {
        if (equal(tok, KW_TYPEDEF) || equal(tok, KW_STATIC) ||
            equal(tok, KW_EXTERN) || equal(tok, KW_INLINE) ||
            equal(tok, PP_THREAD_LOCAL) || equal(tok, PP_THREAD)) {
            if (!attr) error_tok(tok, UNEXPECTED_ST_CL);
            if (equal(tok, KW_TYPEDEF)) attr->is_typedef = true;
            else if (equal(tok, KW_STATIC)) attr->is_static = true;
            else if (equal(tok, KW_EXTERN)) attr->is_extern = true;
            else if (equal(tok, KW_INLINE)) attr->is_inline = true;
            else attr->is_tls = true;
            if (attr->is_typedef &&
                attr->is_static + attr->is_extern + attr->is_inline + attr->is_tls > 1)
                error_tok(tok, INV_TYPEDEF);
            tok = tok->next;
            continue;
        }
        // These keywords are recognized but ignored.
        if (consume(&tok, tok, KW_CONST) || consume(&tok, tok, KW_VOLATILE) ||
            consume(&tok, tok, KW_REGISTER) ||
            consume(&tok, tok, KW_RESTRICT) || consume(&tok, tok, PP_NORETURN))
            continue;
        if (equal(tok, PP_ATOMIC)) {
            tok = tok->next;
            if (equal(tok, PT_PAREN_OPEN)) {
                ty = typename(&tok, tok->next);
                tok = skip(tok, PT_PAREN_CLOSE);
            }
            is_atomic = true;
            continue;
        }
        if (equal(tok, PP_ALIGNAS)) {
            if (!attr) error_tok(tok, UNEXPECTED, PP_ALIGNAS);
            tok = skip(tok->next, PT_PAREN_OPEN);
            if (is_typename(tok)) attr->align = typename(&tok, tok)->align;
            else attr->align = const_expr(&tok, tok);
            tok = skip(tok, PT_PAREN_CLOSE);
            continue;
        }
        // Handle user-defined types
        Type *ty2 = find_typedef(tok);
        if (equal(tok, KW_STRUCT) || equal(tok, KW_UNION) ||
            equal(tok, KW_ENUM) || equal(tok, KW_TYPEOF) || ty2) {
            if (counter) break;
            if (equal(tok, KW_STRUCT)) ty = struct_decl(&tok, tok->next);
            else if (equal(tok, KW_UNION)) ty = union_decl(&tok, tok->next);
            else if (equal(tok, KW_ENUM)) ty = enum_specifier(&tok, tok->next);
            else if (equal(tok, KW_TYPEOF)) ty = typeof_specifier(&tok, tok->next);
            else {
                ty = ty2;
                tok = tok->next;
            }
            counter += OTHER;
            continue;
        }
        // Handle built-in types.
        if (equal(tok, KW_VOID)) counter += VOID;
        else if (equal(tok, KW_BOOL)) counter += BOOL;
        else if (equal(tok, KW_CHAR)) counter += CHAR;
        else if (equal(tok, KW_SHORT)) counter += SHORT;
        else if (equal(tok, KW_INT)) counter += INT;
        else if (equal(tok, KW_LONG)) counter += LONG;
        else if (equal(tok, KW_FLOAT)) counter += FLOAT;
        else if (equal(tok, KW_DOUBLE)) counter += DOUBLE;
        else if (equal(tok, KW_LDOUBLE)) counter += (LONG + DOUBLE);
        else if (equal(tok, KW_UCHAR)) {
            counter += CHAR;
            counter |= UNSIGNED;
        } else if (equal(tok, KW_USHORT)) {
            counter += SHORT;
            counter |= UNSIGNED;
        } else if (equal(tok, KW_UINT)) {
            counter += INT;
            counter |= UNSIGNED;
        }else if (equal(tok, KW_ULONG)) {
            counter += LONG;
            counter |= UNSIGNED;
        } else unreachable()
        switch (counter) {
            case VOID:
                ty = ty_void;
                break;
            case BOOL:
                ty = ty_bool;
                break;
            case CHAR:
                ty = ty_char;
                break;
            case UNSIGNED + CHAR:
                ty = ty_uchar;
                break;
            case SHORT:
                ty = ty_short;
                break;
            case UNSIGNED + SHORT:
                ty = ty_ushort;
                break;
            case INT:
                ty = ty_int;
                break;
            case UNSIGNED + INT:
                ty = ty_uint;
                break;
            case LONG:
                ty = ty_long;
                break;
            case UNSIGNED + LONG:
                ty = ty_ulong;
                break;
            case FLOAT:
                ty = ty_float;
                break;
            case DOUBLE:
                ty = ty_double;
                break;
            case LONG + DOUBLE:
                ty = ty_ldouble;
                break;
            default:
                error_tok(tok, INV_TYPE);
        }
        tok = tok->next;
    }
    if (is_atomic) {
        ty = copy_type(ty);
        ty->is_atomic = true;
    }
    *rest = tok;
    return ty;
}

/// Parse function parameters
static Type *func_params(Token **rest, Token *tok, Type *ty) {
    if (equal(tok, KW_VOID) && equal(tok->next, PT_PAREN_CLOSE)) {
        *rest = tok->next->next;
        return func_type(ty);
    }
    Type head = {};
    Type *cur = &head;
    bool is_variadic = false;
    while (!equal(tok, PT_PAREN_CLOSE)) {
        if (cur != &head) tok = skip(tok, PT_COMMA);
        if (equal(tok, PT_VARARGS)) {
            is_variadic = true;
            tok = tok->next;
            skip(tok, PT_PAREN_CLOSE);
            break;
        }
        Type *ty2 = declspec(&tok, tok, NULL);
        ty2 = declarator(&tok, tok, ty2);
        Token *name = ty2->name;
        if (ty2->kind == TY_ARRAY) {
            // Array of T converted to Pointer to T only in param context
            ty2 = pointer_to(ty2->base);
            ty2->name = name;
        } else if (ty2->kind == TY_FUNC) {
            // Function type converted to Pointer to function only in param context
            ty2 = pointer_to(ty2);
            ty2->name = name;
        }
        cur = cur->next = copy_type(ty2);
    }
    if (cur == &head) is_variadic = true;
    ty = func_type(ty);
    ty->params = head.next;
    ty->is_variadic = is_variadic;
    *rest = tok->next;
    return ty;
}

/// Parse array dimensions
static Type *array_dimensions(Token **rest, Token *tok, Type *ty) {
    while (equal(tok, KW_STATIC) || equal(tok, KW_RESTRICT)) tok = tok->next;
    if (equal(tok, PT_BRACKET_OPEN)) {
        ty = type_suffix(rest, tok->next, ty);
        return array_of(ty, -1);
    }
    Node *expr = conditional(&tok, tok);
    tok = skip(tok, PT_BRACKET_CLOSE);
    ty = type_suffix(rest, tok, ty);
    if (ty->kind == TY_VLA || !is_const_expr(expr)) return is_vla_of(ty, expr);
    return array_of(ty, eval(expr));
}

/// Parse type suffix
static Type *type_suffix(Token **rest, Token *tok, Type *ty) {
    if (equal(tok, PT_PAREN_OPEN)) return func_params(rest, tok->next, ty);
    if (equal(tok, PT_PAREN_CLOSE)) return array_dimensions(rest, tok->next, ty);
    *rest = tok;
    return ty;
}

/// Parse pointers
static Type *pointers(Token **rest, Token *tok, Type *ty) {
    while (consume(&tok, tok, OP_MUL)) {
        ty = pointer_to(ty);
        while (equal(tok, KW_CONST) || equal(tok, KW_VOLATILE) ||
               equal(tok, KW_RESTRICT)) tok = tok->next;
    }
    *rest = tok;
    return ty;
}

/// Parse declarator
static Type *declarator(Token **rest, Token *tok, Type *ty) {
    ty = pointers(&tok, tok, ty);
    if (equal(tok, PT_PAREN_OPEN)) {
        Token *start = tok;
        Type tmp = {};
        declarator(&tok, start->next, &tmp);
        tok = skip(tok, PT_PAREN_CLOSE);
        ty = type_suffix(rest, tok, ty);
        return declarator(&tok, start->next, ty);
    }
    Token *name = NULL;
    Token *name_pos = tok;
    if (tok->kind == TK_IDENT) {
        name = tok;
        tok = tok->next;
    }
    ty = type_suffix(rest, tok, ty);
    ty->name = name;
    ty->name_pos = name_pos;
    return ty;
}

/// Parse abstract declarator
static Type *abstract_declarator(Token **rest, Token *tok, Type *ty) {
    ty = pointers(&tok, tok, ty);
    if (equal(tok, PT_PAREN_OPEN)) {
        Token *start = tok;
        Type tmp = {};
        abstract_declarator(&tok, start->next, &tmp);
        tok = skip(tok, PT_PAREN_CLOSE);
        ty = type_suffix(rest, tok, ty);
        return abstract_declarator(&tok, start->next, ty);
    }
    return type_suffix(rest, tok, ty);
}

/// Parse type name
static Type *typename(Token **rest, Token *tok) {
    Type *ty = declspec(&tok, tok, NULL);
    return abstract_declarator(rest, tok, ty);
}

/// Checks if the given token is the end of a declaration
static bool is_end(Token *tok) {
    return equal(tok, PT_BRACE_CLOSE) || equal(tok, PT_COMMA) || equal(tok->next, PT_BRACE_CLOSE);
}

/// Consume the end of a declaration
static bool consume_end(Token **rest, Token *tok) {
    if (equal(tok, PT_BRACE_CLOSE)) {
        *rest = tok->next;
        return true;
    }
    if (equal(tok, PT_COMMA) && equal(tok->next, PT_BRACE_CLOSE)) {
        *rest = tok->next->next;
        return true;
    }
    return false;
}

/// Parse enum specifier
static Type *enum_specifier(Token **rest, Token *tok) {
    Type *ty = enum_type();
    // Read a structure tag
    Token *tag = NULL;
    if (tok->kind == TK_IDENT) {
        tag = tok;
        tok = tok->next;
    }
    if (tag && !equal(tok, PT_BRACE_OPEN)) {
        Type *ty = find_tag(tag);
        if (!ty) error_tok(tag, UNK_ENUM_TY);
        if (ty->kind != TY_ENUM) error_tok(tag, INV_ENUM_TYPE);
        *rest = tok;
        return ty;
    }
    tok = skip(tok, PT_BRACE_OPEN);
    // Read an enum-list
    int i = 0;
    int val = 0;
    while (!consume_end(rest, tok)) {
        if (i++ > 0) tok = skip(tok, PT_COMMA);
        char *name = get_ident(tok);
        tok = tok->next;
        if (equal(tok, OP_ASSIGN)) val = const_expr(&tok, tok->next);
        VarScope *sc = push_scope(name);
        sc->enum_ty = ty;
        sc->enum_val = val;
    }
    if (tag) push_tag_scope(tag, ty);
    return ty;
}

/// Parse typeof specifier
static Type *typeof_specifier(Token **rest, Token *tok) {
    tok = skip(tok, PT_PAREN_OPEN);
    Type *ty;
    if (is_typename(tok)) ty = typename(&tok, tok);
    else {
        Node *node = expr(&tok, tok);
        add_type(node);
        ty = node->ty;
    }
    *rest = skip(tok, PT_PAREN_CLOSE);
    return ty;
}

/// Compute VLA size
static Node *compute_vla_size(Type *ty, Token *tok) {
    Node *node = new_node(ND_NULL_EXPR, tok);
    if (ty->base) node = new_binary(ND_COMMA, node, compute_vla_size(ty->base, tok), tok);
    if (ty->kind != TY_VLA) return node;
    Node *base_sz;
    if (ty->base->kind == TY_VLA) base_sz = new_var_node(ty->base->vla_size, tok);
    else base_sz = new_num(ty->base->size, tok);
    ty->vla_size = new_lvar("", ty_ulong);
    Node *expr = new_binary(ND_ASSIGN, new_var_node(ty->vla_size, tok),
                            new_binary(ND_MUL, ty->vla_len, base_sz, tok),
                            tok);
    return new_binary(ND_COMMA, node, expr, tok);
}

/// Create allocator
static Node *new_alloca(Node *sz) {
    Node *node = new_unary(ND_FUNCALL, new_var_node(builtin_alloca, sz->tok), sz->tok);
    node->func_ty = builtin_alloca->ty;
    node->ty = builtin_alloca->ty->return_ty;
    node->args = sz;
    add_type(sz);
    return node;
}

/// Parse declaration
static Node *declaration(Token **rest, Token *tok, Type *basety, VarAttr *attr) {
    Node head = {};
    Node *cur = &head;
    int i = 0;
    while (!equal(tok, PT_SEMICOLON)) {
        if (i++ > 0) tok = skip(tok, PT_COMMA);
        Type *ty = declarator(&tok, tok, basety);
        if (ty->kind == TY_VOID) error_tok(tok, VOID_DECLARATION);
        if (!ty->name) error_tok(ty->name_pos, MISSING_VARNAME);
        if (attr && attr->is_static) {
            /// static local var
            Obj *var = new_anon_gvar(ty);
            push_scope(get_ident(ty->name))->var = var;
            if (equal(tok, OP_ASSIGN)) gvar_initializer(&tok, tok->next, var);
            continue;
        }
        cur = cur->next = new_unary(ND_EXPR_STMT, compute_vla_size(ty, tok), tok);
        if (ty->kind == TY_VLA) {
            if (equal(tok, OP_ASSIGN)) error_tok(tok, CANNOT_INIT_VLA);
            /// Variable length arrays (VLAs) are translated to alloca() calls.
            /// For example, `int x[n+2]` is translated to `tmp = n + 2,
            /// x = alloca(tmp)`.
            Obj *var = new_lvar(get_ident(ty->name), ty);
            Token *tok = ty->name;
            Node *expr = new_binary(ND_ASSIGN, new_vla_ptr(var, tok),
                                    new_alloca(new_var_node(ty->vla_size, tok)), tok);
            cur = cur->next = new_unary(ND_EXPR_STMT, expr, tok);
            continue;
        }
        Obj *var = new_lvar(get_ident(ty->name), ty);
        if (attr && attr->align) var->align = attr->align;
        if (equal(tok, OP_ASSIGN)) {
            Node *expr = lvar_initializer(&tok, tok->next, var);
            cur = cur->next = new_unary(ND_EXPR_STMT, expr, tok);
        }
        if (var->ty->size < 0) error_tok(ty->name, INCOMPLETE_TYPE);
        if (var->ty->kind == TY_VOID) error_tok(ty->name, VOID_DECLARATION);
    }
    Node *node = new_node(ND_BLOCK, tok);
    node->body = head.next;
    *rest = tok->next;
    return node;
}

/// Skip excess element
static Token *skip_excess_element(Token *tok) {
    if (equal(tok, PT_BRACE_OPEN)) {
        tok = skip_excess_element(tok->next);
        return skip(tok, PT_BRACE_CLOSE);
    }
    assign(&tok, tok);
    return tok;
}

/// Parse string initializer
static void string_initializer(Token **rest, Token *tok, Initializer *init) {
    if (init->is_flexible)
        *init = *new_initializer(array_of(init->ty->base, tok->ty->array_len), false);
    int len = MIN(init->ty->array_len, tok->ty->array_len);
    switch (init->ty->base->size) {
        case 1: {
            char *str = tok->str;
            for (int i = 0; i < len; i++) init->children[i]->expr = new_num(str[i], tok);
            break;
        }
        case 2: {
            uint16_t *str = (uint16_t *)tok->str;
            for (int i = 0; i < len; i++) init->children[i]->expr = new_num(str[i], tok);
            break;
        }
        case 4: {
            uint32_t *str = (uint32_t *)tok->str;
            for (int i = 0; i < len; i++) init->children[i]->expr = new_num(str[i], tok);
            break;
        }
        default: unreachable();
    }
    *rest = tok->next;
}

/// C99 added the designated initializer to the language, which allows
/// programmers to move the "cursor" of an initializer to any element.
/// The syntax looks like this:
///
///   int x[10] = { 1, 2, [5]=3, 4, 5, 6, 7 };
///
/// `[5]` moves the cursor to the 5th element, so the 5th element of x
/// is set to 3. Initialization then continues forward in order, so
/// 6th, 7th, 8th and 9th elements are initialized with 4, 5, 6 and 7,
/// respectively. Unspecified elements (in this case, 3rd and 4th
/// elements) are initialized with zero.
///
/// Nesting is allowed, so the following initializer is valid:
///
///   int x[5][10] = { [5][8]=1, 2, 3 };
///
/// It sets x[5][8], x[5][9] and x[6][0] to 1, 2 and 3, respectively.
///
/// Use `.fieldname` to move the cursor for a struct initializer. E.g.
///
///   struct { int a, b, c; } x = { .c=5 };
///
/// The above initializer sets x.c to 5.
static void array_designator(Token **rest, Token *tok, Type *ty, int *begin, int *end) {
    *begin = const_expr(&tok, tok->next);
    if (*begin >= ty->array_len) error_tok(tok, DESIGNATOR_OOB);
    if (equal(tok, PT_VARARGS)) {
        *end = const_expr(&tok, tok->next);
        if (*end >= ty->array_len) error_tok(tok, DESIGNATOR_OOB);
        if (*end < *begin) error_tok(tok, DESIGNATOR_RANGE_EMPTY, *begin, *end);
    } else {
        *end = *begin;
    }
    *rest = skip(tok, PT_BRACKET_CLOSE);
}

/// Parse structure designator
static Member *struct_designator(Token **rest, Token *tok, Type *ty) {
    Token *start = tok;
    tok = skip(tok, PT_POINT);
    if (tok->kind != TK_IDENT) error_tok(tok, EXPECTED_MEM_NAME);
    for (Member *mem = ty->members; mem; mem = mem->next) {
        /// Anonymous struct member
        if (mem->ty->kind == TY_STRUCT && !mem->name) {
            if (get_struct_member(mem->ty, tok)) {
                *rest = start;
                return mem;
            }
            continue;
        }
        /// Regular struct member
        if (mem->name->len == tok->len && !strncmp(mem->name->loc, tok->loc, tok->len)) {
            *rest = tok->next;
            return mem;
        }
    }
    error_tok(tok, NO_SUCH_MEMBER);
}

/// Parse designation initializer
static void designation(Token **rest, Token *tok, Initializer *init) {
    if (equal(tok, PT_BRACKET_OPEN)) {
        if (init->ty->kind != TY_ARRAY) error_tok(tok, NOT_ARRAY_INIT);
        int begin, end;
        array_designator(&tok, tok, init->ty, &begin, &end);
        Token *tok2;
        for (int i = begin; i <= end; i++) designation(&tok2, tok, init->children[i]);
        array_initializer2(rest, tok2, init, begin + 1);
        return;
    }
    if (equal(tok, PT_POINT) && init->ty->kind == TY_STRUCT) {
        Member *mem = struct_designator(&tok, tok, init->ty);
        designation(&tok, tok, init->children[mem->idx]);
        init->expr = NULL;
        struct_initializer2(rest, tok, init, mem->next);
        return;
    }
    if (equal(tok, PT_POINT) && init->ty->kind == TY_UNION) {
        Member *mem = struct_designator(&tok, tok, init->ty);
        init->mem = mem;
        designation(rest, tok, init->children[mem->idx]);
        return;
    }
    if (equal(tok, PT_POINT)) error_tok(tok, FIEND_NAME);
    if (equal(tok, OP_ASSIGN)) tok = tok->next;
    initializer2(rest, tok, init);
}

/// Count the number of elements in an array initializer
static int count_array_init_elements(Token *tok, Type *ty) {
    bool first = true;
    Initializer *dummy = new_initializer(ty->base, true);
    int i = 0, max = 0;
    while (!consume_end(&tok, tok)) {
        if (!first) tok = skip(tok, PT_COMMA);
        first = false;
        if (equal(tok, PT_BRACKET_OPEN)) {
            i = const_expr(&tok, tok->next);
            if (equal(tok, PT_VARARGS)) i = const_expr(&tok, tok->next);
            tok = skip(tok, PT_BRACKET_CLOSE);
            designation(&tok, tok, dummy);
        } else {
            initializer2(&tok, tok, dummy);
        }
        i++;
        max = MAX(max, i);
    }
    return max;
}

/// Parse array initializer
static void array_initializer1(Token **rest, Token *tok, Initializer *init) {
    tok = skip(tok, PT_BRACE_OPEN);
    if (init->is_flexible) {
        int len = count_array_init_elements(tok, init->ty);
        *init = *new_initializer(array_of(init->ty->base, len), false);
    }
    bool first = true;
    if (init->is_flexible) {
        int len = count_array_init_elements(tok, init->ty);
        *init = *new_initializer(array_of(init->ty->base, len), false);
    }
    for (int i = 0; !consume_end(rest, tok); i++) {
        if (!first) tok = skip(tok, PT_COMMA);
        first = false;
        if (equal(tok, PT_BRACKET_OPEN)) {
            int begin, end;
            array_designator(&tok, tok, init->ty, &begin, &end);
            Token *tok2;
            for (int j = begin; j <= end; j++) designation(&tok2, tok, init->children[j]);
            tok = tok2;
            i = end;
            continue;
        }
        if (i < init->ty->array_len) initializer2(&tok, tok, init->children[i]);
        else tok = skip_excess_element(tok);
    }
}

/// Parse array initializer
static void array_initializer2(Token **rest, Token *tok, Initializer *init, int i) {
    if (init->is_flexible) {
        int len = count_array_init_elements(tok, init->ty);
        *init = *new_initializer(array_of(init->ty->base, len), false);
    }
    for (; i < init->ty->array_len && !is_end(tok); i++) {
        Token *start = tok;
        if (i > 0) tok = skip(tok, PT_COMMA);
        if (equal(tok, PT_BRACKET_OPEN) || equal(tok, PT_POINT)) {
            *rest = start;
            return;
        }
        initializer2(&tok, tok, init->children[i]);
    }
    *rest = tok;
}

/// Parse struct initializer
static void struct_initializer1(Token **rest, Token *tok, Initializer *init) {
    tok = skip(tok, PT_BRACE_OPEN);
    Member *mem = init->ty->members;
    bool first = true;
    while (!consume_end(rest, tok)) {
        if (!first) tok = skip(tok, PT_COMMA);
        first = false;
        if (equal(tok, PT_POINT)) {
            mem = struct_designator(&tok, tok, init->ty);
            designation(&tok, tok, init->children[mem->idx]);
            mem = mem->next;
            continue;
        }
        if (mem) {
            initializer2(&tok, tok, init->children[mem->idx]);
            mem = mem->next;
        } else {
            tok = skip_excess_element(tok);
        }
    }
}

/// Parse struct initializer
static void struct_initializer2(Token **rest, Token *tok, Initializer *init, Member *mem) {
    bool first = true;
    for (; mem && !is_end(tok); mem = mem->next) {
        Token *start = tok;
        if (!first) tok = skip(tok, PT_COMMA);
        first = false;
        if (equal(tok, PT_BRACKET_OPEN) || equal(tok, PT_POINT)) {
            *rest = start;
            return;
        }
        initializer2(&tok, tok, init->children[mem->idx]);
    }
    *rest = tok;
}

/// Parse union initializer
static void union_initializer(Token **rest, Token *tok, Initializer *init) {
    /// Unlike structs, union initializers take only one initializer,
    /// and that initializes the first union member by default.
    /// You can initialize other member using a designated initializer.
    if (equal(tok, PT_BRACE_OPEN) && equal(tok->next, PT_POINT)) {
        Member *mem = struct_designator(&tok, tok->next, init->ty);
        init->mem = mem;
        designation(&tok, tok, init->children[mem->idx]);
        *rest = skip(tok, PT_BRACE_CLOSE);
        return;
    }
    init->mem = init->ty->members;
    if (equal(tok, PT_BRACE_OPEN)) {
        initializer2(&tok, tok->next, init->children[0]);
        consume(&tok, tok, PT_COMMA);
        *rest = skip(tok, PT_BRACE_CLOSE);
    } else {
        initializer2(rest, tok, init->children[0]);
    }
}

/// Parse initializer
static void initializer2(Token **rest, Token *tok, Initializer *init) {
    if (init->ty->kind == TY_ARRAY && tok->kind == TK_STR) {
        string_initializer(rest, tok, init);
        return;
    }
    if (init->ty->kind == TY_ARRAY) {
        if (equal(tok, PT_BRACE_OPEN)) array_initializer1(rest, tok, init);
        else array_initializer2(rest, tok, init, 0);
        return;
    }
    if (init->ty->kind == TY_STRUCT) {
        if (equal(tok, PT_BRACE_OPEN)) {
            struct_initializer1(rest, tok, init);
            return;
        }
        /// A struct can be initialized with another struct. E.g.
        /// `struct T x = y;` where y is a variable of type `struct T`.
        /// Handle that case first.
        Node *expr = assign(rest, tok);
        add_type(expr);
        if (expr->ty->kind == TY_STRUCT) {
            init->expr = expr;
            return;
        }
        struct_initializer2(rest, tok, init, init->ty->members);
        return;
    }
    if (init->ty->kind == TY_UNION) {
        union_initializer(rest, tok, init);
        return;
    }
    if (equal(tok, PT_BRACE_OPEN)) {
        /// An initializer for a scalar variable can be surrounded by
        /// braces. E.g. `int x = {3};`. Handle that case.
        initializer2(&tok, tok->next, init);
        *rest = skip(tok, PT_BRACE_CLOSE);
        return;
    }
    init->expr = assign(rest, tok);
}

/// Copies a struct type
static Type *copy_struct_type(Type *ty) {
    ty = copy_type(ty);
    Member head = {};
    Member *cur = &head;
    for (Member *mem = ty->members; mem; mem = mem->next) {
        Member *m = calloc(1, sizeof(Member));
        *m = *mem;
        cur = cur->next = m;
    }
    ty->members = head.next;
    return ty;
}

/// Parse initializer
static Initializer *initializer(Token **rest, Token *tok, Type *ty, Type **new_ty) {
    Initializer *init = new_initializer(ty, true);
    initializer2(rest, tok, init);
    if ((ty->kind == TY_STRUCT || ty->kind == TY_UNION) && ty->is_flexible) {
        ty = copy_struct_type(ty);
        Member *mem = ty->members;
        while (mem->next) mem = mem->next;
        mem->ty = init->children[mem->idx]->ty;
        ty->size += mem->ty->size;
        *new_ty = ty;
        return init;
    }
    *new_ty = init->ty;
    return init;
}

/// Initialize designator expression
static Node *init_desg_expr(InitDesg *desg, Token *tok) {
    if (desg->var) return new_var_node(desg->var, tok);
    if (desg->member) {
        Node *node = new_unary(ND_MEMBER, init_desg_expr(desg->next, tok), tok);
        node->member = desg->member;
        return node;
    }
    Node *lhs = init_desg_expr(desg->next, tok);
    Node *rhs = new_num(desg->idx, tok);
    return new_unary(ND_DEREF, new_add(lhs, rhs, tok), tok);
}

/// Create a local variable initializer
static Node *create_lvar_init(Initializer *init, Type *ty, InitDesg *desg, Token *tok) {
    if (ty->kind == TY_ARRAY) {
        Node *node = new_node(ND_NULL_EXPR, tok);
        for (int i = 0; i < ty->array_len; i++) {
            InitDesg  desg2 = {desg, i};
            Node *rhs = create_lvar_init(init->children[i], ty->base, &desg2, tok);
            node = new_binary(ND_COMMA, node, rhs, tok);
        }
        return node;
    }
    if (ty->kind == TY_STRUCT || !init->expr) {
        Node *node = new_node(ND_NULL_EXPR, tok);
        for (Member *mem = ty->members; mem; mem = mem->next) {
            InitDesg desg2 = {desg, 0, mem};
            Node *rhs = create_lvar_init(init->children[mem->idx], mem->ty, &desg2, tok);
            node = new_binary(ND_COMMA, node, rhs, tok);
        }
        return node;
    }
    if (ty->kind == TY_UNION) {
        Member *mem = init->mem ? init->mem : ty->members;
        InitDesg desg2 = {desg, 0, mem};
        return create_lvar_init(init->children[mem->idx], mem->ty, &desg2, tok);
    }
    if (!init->expr) return new_node(ND_NULL_EXPR, tok);
    Node *lhs = init_desg_expr(desg, tok);
    return new_binary(ND_ASSIGN, lhs, init->expr, tok);
}

/// Parse local variable initializer
/// A variable definition with an initializer is a shorthand notation
/// for a variable definition followed by assignments. This function
/// generates assignment expressions for an initializer. For example,
/// `int x[2][2] = {{6, 7}, {8, 9}}` is converted to the following
/// expressions:
///
///   x[0][0] = 6;
///   x[0][1] = 7;
///   x[1][0] = 8;
///   x[1][1] = 9;
static Node *lvar_initializer(Token **rest, Token *tok, Obj *var) {
    Initializer *init = initializer(rest, tok, var->ty, &var->ty);
    InitDesg desg = {NULL, 0, NULL, var};
    Node *lhs = new_node(ND_MEMZERO, tok);
    lhs->var = var;
    Node *rhs = create_lvar_init(init, var->ty, &desg, tok);
    return new_binary(ND_COMMA, lhs, rhs, tok);
}

/// Read a buffer as a number with the given size
static uint64_t read_buf(char *buf, int sz) {
    if (sz == 1) return *buf;
    if (sz == 2) return *(uint16_t *)buf;
    if (sz == 4) return *(uint32_t *)buf;
    if (sz == 8) return *(uint64_t *)buf;
    unreachable();
}

/// Write a number to a buffer
static void write_buf(char *buf, uint64_t val, int sz) {
    if (sz == 1) *buf = val;
    else if (sz == 2) *(uint16_t *)buf = val;
    else if (sz == 4) *(uint32_t *)buf = val;
    else if (sz == 8) *(uint64_t *)buf = val;
    else unreachable();
}

static Relocation *write_gvar_data(Relocation *cur, Initializer *init, Type *ty, char *buf, int offset) {
    if (ty->kind == TY_ARRAY) {
        int sz = ty->base->size;
        for (int i = 0; i < ty->array_len; i++)
            cur = write_gvar_data(cur, init->children[i], ty->base, buf, offset);
        return cur;
    }
    if (ty->kind == TY_STRUCT) {
        for (Member *mem = ty->members; mem; mem = mem->next) {
            if (mem->is_bitfield) {
                Node *expr = init->children[mem->idx]->expr;
                if (!expr) break;
                char *loc = buf + offset + mem->offs;
                uint64_t oldval = read_buf(loc, mem->ty->size);
                uint64_t newval = eval(expr);
                uint64_t mask = (1L << mem->bit_width) - 1;
                uint64_t combined = oldval | ((newval & mask) << mem->bit_offs);
                write_buf(loc, combined, mem->ty->size);
            } else {
                cur = write_gvar_data(cur, init->children[mem->idx], mem->ty, buf, offset + mem->offs);
            }
        }
        return cur;
    }
    if (ty->kind == TY_UNION) {
        if (!init->mem) return cur;
        return write_gvar_data(cur, init->children[init->mem->idx], init->mem->ty, buf, offset);
    }
    if (!init->expr) return cur;
    if (ty->kind == TY_FLOAT) {
        *(float *)(buf + offset) = eval_double(init->expr);
        return cur;
    }
    if (ty->kind == TY_DOUBLE) {
        *(double *)(buf + offset) = eval_double(init->expr);
        return cur;
    }
    char **label = NULL;
    uint64_t val = eval2(init->expr, &label);
    if (!label) {
        write_buf(buf + offset, val, ty->size);
        return cur;
    }
    Relocation *rel = calloc(1, sizeof(Relocation));
    rel->offset = offset;
    rel->label = label;
    rel->addend = val;
    cur->next = rel;
    return cur->next;
}

/// Initializers for global variables are evaluated at compile-time and
/// embedded to .data section. This function serializes Initializer
/// objects to a flat byte array. It is a compile error if an
/// initializer list contains a non-constant expression.
static void gvar_initializer(Token **rest, Token *tok, Obj *var) {
    Initializer *init = initializer(rest, tok, var->ty, &var->ty);
    Relocation head = {};
    char *buf = calloc(1, var->ty->size);
    write_gvar_data(&head, init, var->ty, buf, 0);
    var->init_data = buf;
    var->rel = head.next;
}

/// Check if a token is a typename
static bool is_typename(Token *tok) {
    static HashMap map;
    if (map.capacity == 0) {
        static char *kw[] = {
                KW_VOID, KW_BOOL, KW_CHAR, KW_UCHAR, KW_SHORT, KW_USHORT, KW_INT,
                KW_UINT,KW_LONG,KW_ULONG, KW_STRUCT,KW_UNION,KW_TYPEDEF, KW_ENUM,
                KW_STATIC,KW_EXTERN,PP_ALIGNAS,KW_CONST, KW_VOLATILE, KW_REGISTER,
                KW_RESTRICT,PP_NORETURN,KW_FLOAT, KW_DOUBLE, KW_LDOUBLE,KW_TYPEOF,
                KW_INLINE,PP_THREAD_LOCAL,PP_THREAD,PP_ATOMIC
        };
        for (int i = 0; i < sizeof(kw) / sizeof(*kw); i++) hashmap_put(&map, kw[i], (void *)1);
    }
    return hashmap_get_wlen(&map, tok->loc, tok->len) || find_typedef(tok);
}

/// Parse asm statement
static Node *asm_stmt(Token **rest, Token *tok) {
    Node *node = new_node(ND_ASM, tok);
    tok = tok->next;
    while (equal(tok, KW_VOLATILE) || equal(tok, KW_INLINE)) tok = tok->next;
    tok = skip(tok, PT_PAREN_OPEN);
    if (tok->kind != TK_STR || tok->ty->base->kind != TY_CHAR) error_tok(tok, EXPECTED_STR_LITERAL);
    node->asm_str = tok->str;
    *rest = skip(tok->next, PT_PAREN_CLOSE);
    return node;
}

static Node *stmt(Token **rest, Token *tok) {
    if (equal(tok, KW_RETURN)) {
        Node *node = new_node(ND_RETURN, tok);
        if (consume(rest, tok->next, PT_SEMICOLON)) return node;
        Node *exp = expr(&tok, tok->next);
        *rest = skip(tok, PT_SEMICOLON);
        add_type(exp);
        Type *ty = current_fn->ty->return_ty;
        if (ty->kind != TY_STRUCT && ty->kind != TY_UNION) exp = new_cast(exp, current_fn->ty->return_ty);
        node->lhs = exp;
        return node;
    }
    if (equal(tok, KW_IF)) {
        Node *node = new_node(ND_IF, tok);
        tok = skip(tok->next, PT_PAREN_OPEN);
        node->cond = expr(&tok, tok);
        tok = skip(tok, PT_PAREN_CLOSE);
        node->then = stmt(&tok, tok);
        if (equal(tok, KW_ELSE)) node->els = stmt(&tok, tok->next);
        *rest = tok;
        return node;
    }
    if (equal(tok, KW_SWITCH)) {
        Node *node = new_node(ND_SWITCH, tok);
        tok = skip(tok->next, PT_PAREN_OPEN);
        node->cond = expr(&tok, tok);
        tok = skip(tok, PT_PAREN_CLOSE);
        Node *sw = current_switch;
        current_switch = node;
        char *brk = brk_label;
        brk_label = node->brk_label = new_unique_name();
        node->then = stmt(rest, tok);
        current_switch = sw;
        brk_label = brk;
        return node;
    }
    if (equal(tok, KW_CASE)) {
        if (!current_switch) error_tok(tok, STRAY_PP_TOKEN, KW_CASE);
        Node *node = new_node(ND_CASE, tok);
        int begin = const_expr(&tok, tok->next);
        int end;
        if (equal(tok, PT_VARARGS)) {
            end = const_expr(&tok, tok->next);
            if (end < begin) error_tok(tok, CASE_RANGE_EMPTY, begin, end);
        } else {
            end = begin;
        }
        tok = skip(tok, PT_COLON);
        node->label = new_unique_name();
        node->lhs = stmt(rest, tok);
        node->begin = begin;
        node->end = end;
        node->case_next = current_switch->case_next;
        current_switch->case_next = node;
        return node;
    }
    if (equal(tok, KW_FOR)) {
        Node *node = new_node(ND_FOR, tok);
        tok = skip(tok->next, PT_PAREN_OPEN);
        enter_scope();
        char *brk = brk_label;
        char *cont = cont_label;
        brk_label = node->brk_label = new_unique_name();
        cont_label = node->cont_label = new_unique_name();
        if (is_typename(tok)) {
            Type *basety = declspec(&tok, tok, NULL);
            node->init = declaration(&tok, tok, basety, NULL);
        } else {
            node->init = expr(&tok, tok);
        }
        if (!equal(tok, PT_SEMICOLON)) node->cond = expr(&tok, tok);
        tok = skip(tok, PT_SEMICOLON);
        if (!equal(tok, PT_PAREN_CLOSE)) node->inc = expr(&tok, tok);
        tok = skip(tok, PT_PAREN_CLOSE);
        node->then = stmt(&tok, tok);
        leave_scope();
        brk_label = brk;
        cont_label = cont;
        return node;
    }
    if (equal(tok, KW_WHILE)) {
        Node *node = new_node(ND_FOR, tok);
        tok = skip(tok->next, PT_PAREN_OPEN);
        node->cond = expr(&tok, tok);
        tok = skip(tok, PT_PAREN_CLOSE);
        char *brk = brk_label;
        char *cont = cont_label;
        brk_label = node->brk_label = new_unique_name();
        cont_label = node->cont_label = new_unique_name();
        node->then = stmt(&tok, tok);
        brk_label = brk;
        cont_label = cont;
        return node;
    }
    if (equal(tok, KW_DO)) {
        Node *node = new_node(ND_DO, tok);
        char *brk = brk_label;
        char *cont = cont_label;
        brk_label = node->brk_label = new_unique_name();
        cont_label = node->cont_label = new_unique_name();
        node->then = stmt(&tok, tok->next);
        brk_label = brk;
        cont_label = cont;
        tok = skip(tok, KW_WHILE);
        tok = skip(tok->next, PT_PAREN_OPEN);
        node->cond = expr(&tok, tok);
        tok = skip(tok, PT_PAREN_CLOSE);
        *rest = skip(tok, PT_SEMICOLON);
        return node;
    }
    if (equal(tok, PP_ASM)) return asm_stmt(rest, tok);
    if (equal(tok, KW_GOTO)) {
        if (equal(tok->next, OP_MUL)) {
            Node *node = new_node(ND_GOTO_EXPR, tok);
            node->lhs = expr(&tok, tok->next->next);
            *rest = skip(tok, PT_SEMICOLON);
            return node;
        }
        Node *node = new_node(ND_GOTO, tok);
        node->label = get_ident(tok->next);
        node->goto_next = gotos;
        gotos = node;
        *rest = skip(tok, PT_SEMICOLON);
        return node;
    }
    if (equal(tok, KW_BREAK)) {
        if (!brk_label) error_tok(tok, STRAY_PP_TOKEN, KW_BREAK);
        Node *node = new_node(ND_GOTO, tok);
        node->unique_label = brk_label;
        *rest = skip(tok, PT_SEMICOLON);
        return node;
    }
    if (equal(tok, KW_CONTINUE)) {
        if (!cont_label) error_tok(tok, STRAY_PP_TOKEN, KW_CONTINUE);
        Node *node = new_node(ND_GOTO, tok);
        node->unique_label = cont_label;
        *rest = skip(tok, PT_SEMICOLON);
        return node;
    }
    if (tok->kind == TK_IDENT && equal(tok->next, PT_COLON)) {
        Node *node = new_node(ND_LABEL, tok);
        node->label = strndup(tok->loc, tok->len);
        node->unique_label = new_unique_name();
        node->lhs = stmt(rest, tok->next->next);
        node->goto_next = labels;
        labels = node;
        return node;
    }
    if (equal(tok, PT_BRACE_OPEN)) return compound_stmt(rest, tok->next);
    return expr_stmt(rest, tok);
}

/// Parse compound statement
static Node *compound_stmt(Token **rest, Token *tok) {
    Node *node = new_node(ND_BLOCK, tok);
    Node head = {};
    Node *cur = &head;
    enter_scope();
    while (!equal(tok, PT_BRACE_CLOSE)) {
        if (is_typename(tok) && !equal(tok->next, PT_COLON)) {
            VarAttr attr = {};
            Type *basety = declspec(&tok, tok, &attr);
            if (attr.is_typedef) {
                tok = parse_typedef(tok, basety);
                continue;
            }
            if (is_function(tok)) {
                tok = function(tok, basety, &attr);
                continue;
            }
            cur = cur->next = declaration(&tok, tok, basety, &attr);
        } else {
            cur = cur->next = stmt(&tok, tok);
        }
        add_type(cur);
    }
    leave_scope();
    node->body = head.next;
    *rest = tok->next;
    return node;
}

/// Parse expression statement
static Node *expr_stmt(Token **rest, Token *tok) {
    if (equal(tok, PT_SEMICOLON)) {
        *rest = tok->next;
        return new_node(ND_BLOCK, tok);
    }
    Node *node = new_node(ND_EXPR_STMT, tok);
    node->lhs = expr(&tok, tok);
    *rest = skip(tok, PT_SEMICOLON);
    return node;
}

static Node *expr(Token **rest, Token *tok) {
    Node *node = assign(&tok, tok);
    if (equal(tok, PT_COMMA)) return new_binary(ND_COMMA, node, expr(rest, tok->next), tok);
    *rest = tok;
    return node;
}

/// Evaluate an expression
static int64_t eval(Node *node) {
    return eval2(node, NULL);
}

/// Evaluate a given node as a constant expression.
///
/// A constant expression is either just a number or ptr+n where ptr
/// is a pointer to a global variable and n is a positive/negative
/// number. The latter form is accepted only as an initialization
/// expression for a global variable
static int64_t eval2(Node *node, char ***label) {
    add_type(node);
    if (is_flonum(node->ty)) return eval_double(node);
    switch (node->kind) {
        case ND_ADD:
            return eval2(node->lhs, label) + eval(node->rhs);
        case ND_SUB:
            return eval2(node->lhs, label) - eval(node->rhs);
        case ND_MUL:
            return eval(node->lhs) * eval(node->rhs);
        case ND_DIV:
            if (node->ty->is_unsigned) return (uint64_t)eval(node->lhs) / eval(node->rhs);
            return eval(node->lhs) / eval(node->rhs);
        case ND_NEG:
            return -eval(node->lhs);
        case ND_MOD:
            if (node->ty->is_unsigned) return (uint64_t)eval(node->lhs) % eval(node->rhs);
            return eval(node->lhs) % eval(node->rhs);
        case ND_BITAND:
            return eval(node->lhs) & eval(node->rhs);
        case ND_BITOR:
            return eval(node->lhs) | eval(node->rhs);
        case ND_BITXOR:
            return eval(node->lhs) ^ eval(node->rhs);
        case ND_SHL:
            return eval(node->lhs) << eval(node->rhs);
        case ND_SHR:
            if (node->ty->is_unsigned && node->ty->size == 8) return (uint64_t)eval(node->lhs) >> eval(node->rhs);
            return eval(node->lhs) >> eval(node->rhs);
        case ND_EQ:
            return eval(node->lhs) == eval(node->rhs);
        case ND_NE:
            return eval(node->lhs) != eval(node->rhs);
        case ND_LT:
            if (node->lhs->ty->is_unsigned) return (uint64_t)eval(node->lhs) < eval(node->rhs);
            return eval(node->lhs) < eval(node->rhs);
        case ND_LE:
            if (node->lhs->ty->is_unsigned) return (uint64_t)eval(node->lhs) <= eval(node->rhs);
            return eval(node->lhs) <= eval(node->rhs);
        case ND_COND:
            return eval(node->cond) ? eval2(node->then, label) : eval2(node->els, label);
        case ND_COMMA:
            return eval2(node->rhs, label);
        case ND_NOT:
            return !eval(node->lhs);
        case ND_BITNOT:
            return ~eval(node->lhs);
        case ND_LOGAND:
            return eval(node->lhs) && eval(node->rhs);
        case ND_LOGOR:
            return eval(node->lhs) || eval(node->rhs);
        case ND_CAST: {
            int64_t val = eval2(node->lhs, label);
            if (is_int(node->ty)) {
                switch (node->ty->size) {
                    case 1: return node->ty->is_unsigned ? (uint8_t)val : (int8_t)val;
                    case 2: return node->ty->is_unsigned ? (uint16_t)val : (int16_t)val;
                    case 4: return node->ty->is_unsigned ? (uint32_t)val : (int32_t)val;
                }
            }
            return val;
        }
        case ND_ADDR:
            return eval_rval(node->lhs, label);
        case ND_LABEL_VAL:
            *label = &node->unique_label;
            return 0;
        case ND_MEMBER:
            if (!label) error_tok(node->tok, NOT_CT_CONST);
            if (node->ty->kind != TY_ARRAY) error_tok(node->tok, INVALID_INIT);
            return eval_rval(node->lhs, label) + node->member->offs;
        case ND_VAR:
            if (!label) error_tok(node->tok, NOT_CT_CONST);
            if (node->var->ty->kind != TY_ARRAY && node->var->ty->kind != TY_FUNC)
                error_tok(node->tok, INVALID_INIT);
            *label = &node->var->name;
            return 0;
        case ND_NUM:
            return node->val;
    }
    error_tok(node->tok, NOT_CT_CONST);
}

static int64_t eval_rval(Node *node, char ***label) {
    switch (node->kind) {
        case ND_VAR:
            if (node->var->is_local) error_tok(node->tok, NOT_CT_CONST);
            *label = &node->var->name;
            return 0;
        case ND_DEREF:
            return eval2(node->lhs, label);
        case ND_MEMBER:
            return eval_rval(node->lhs, label) + node->member->offs;
    }
    error_tok(node->tok, INVALID_INIT);
}

/// Check if a node is a compile-time constant expression
static bool is_const_expr(Node *node) {
    add_type(node);
    switch (node->kind) {
        case ND_ADD: case ND_SUB: case ND_MUL: case ND_DIV: case ND_BITAND: case ND_BITOR: case ND_BITXOR: case ND_SHL:
            case ND_SHR: case ND_EQ: case ND_NE: case ND_LT: case ND_LE: case ND_LOGAND: case ND_LOGOR:
            return is_const_expr(node->lhs) && is_const_expr(node->rhs);
        case ND_COND:
            if (!is_const_expr(node->cond)) return false;
            return is_const_expr(eval(node->cond) ? node->then : node->els);
        case ND_COMMA:
            return is_const_expr(node->rhs);
        case ND_NEG: case ND_NOT: case ND_BITNOT: case ND_CAST:
            return is_const_expr(node->lhs);
        case ND_NUM:
            return true;
    }
    return false;
}

/// Parse a compile-time constant expression
int64_t const_expr(Token **rest, Token *tok) {
    Node *node = conditional(rest, tok);
    return eval(node);
}

static double eval_double(Node *node) {
    add_type(node);
    if (is_int(node->ty)) {
        if (node->ty->is_unsigned) return (unsigned long)eval(node);
        return eval(node);
    }
    switch (node->kind) {
        case ND_ADD:
            return eval_double(node->lhs) + eval_double(node->rhs);
        case ND_SUB:
            return eval_double(node->lhs) - eval_double(node->rhs);
        case ND_MUL:
            return eval_double(node->lhs) * eval_double(node->rhs);
        case ND_DIV:
            return eval_double(node->lhs) / eval_double(node->rhs);
        case ND_NEG:
            return -eval_double(node->lhs);
        case ND_COND:
            return eval_double(node->cond) ? eval_double(node->then) : eval_double(node->els);
        case ND_COMMA:
            return eval_double(node->rhs);
        case ND_CAST:
            if (is_flonum(node->lhs->ty)) return eval_double(node->lhs);
            return eval(node->lhs);
        case ND_NUM:
            return node->fval;
    }
    error_tok(node->tok, NOT_CT_CONST);
}

/// Convert `A.x op= C` to `tmp = &A, (*tmp).x = (*tmp).x op C`.
static Node *to_assign(Node *binary) {
    add_type(binary->lhs);
    add_type(binary->rhs);
    Token *tok = binary->tok;
    if (binary->lhs->kind == ND_MEMBER) {
        Obj *var = new_lvar("", pointer_to(binary->lhs->lhs->ty));
        Node *expr1 = new_binary(ND_ASSIGN, new_var_node(var, tok),
                                new_unary(ND_ADDR, binary->lhs->lhs, tok),
                                tok);
        Node *expr2 = new_unary(ND_MEMBER,
                                new_unary(ND_DEREF, new_var_node(var, tok), tok),
                                tok);
        expr2->member = binary->lhs->member;
        Node *expr3 = new_unary(ND_MEMBER,
                                new_unary(ND_DEREF, new_var_node(var, tok), tok),
                                tok);
        expr3->member = binary->lhs->member;
        Node *expr4 = new_binary(ND_ASSIGN, expr2,
                                 new_binary(binary->kind, expr3, binary->rhs, tok),
                                 tok);
        return new_binary(ND_COMMA, expr1, expr4, tok);
    }
    /// If A is an atomic type, Convert `A op= B` to
    ///
    /// ({
    ///   T1 *addr = &A; T2 val = (B); T1 old = *addr; T1 new;
    ///   do {
    ///    new = old op val;
    ///   } while (!atomic_compare_exchange_strong(addr, &old, new));
    ///   new;
    /// })
    if (binary->lhs->ty->is_atomic) {
        Node head = {};
        Node *cur = &head;
        Obj *addr = new_lvar("", pointer_to(binary->lhs->ty));
        Obj *val = new_lvar("", binary->lhs->ty);
        Obj *old = new_lvar("", binary->lhs->ty);
        Obj *new = new_lvar("", binary->lhs->ty);
        cur = cur->next =
                new_unary(ND_EXPR_STMT,
                          new_binary(ND_ASSIGN, new_var_node(addr, tok),
                                     new_unary(ND_ADDR, binary->lhs, tok), tok),
                          tok);
        cur = cur->next =
                new_unary(ND_EXPR_STMT,
                          new_binary(ND_ASSIGN, new_var_node(val, tok), binary->rhs, tok),
                          tok);
        cur = cur->next =
                new_unary(ND_EXPR_STMT,
                          new_binary(ND_ASSIGN, new_var_node(old, tok),
                                     new_unary(ND_DEREF, new_var_node(addr, tok), tok), tok),
                          tok);
        Node *loop = new_node(ND_DO, tok);
        loop->brk_label = new_unique_name();
        loop->cont_label = new_unique_name();
        Node *body = new_binary(ND_ASSIGN,
                                new_var_node(new, tok),
                                new_binary(binary->kind, new_var_node(old, tok),
                                           new_var_node(val, tok), tok),
                                tok);
        loop->then = new_node(ND_BLOCK, tok);
        loop->then->body = new_unary(ND_EXPR_STMT, body, tok);
        Node *cas = new_node(ND_CAS, tok);
        cas->cas_addr = new_var_node(addr, tok);
        cas->cas_old = new_unary(ND_ADDR, new_var_node(old, tok), tok);
        cas->cas_new = new_var_node(new, tok);
        loop->cond = new_unary(ND_NOT, cas, tok);
        cur = cur->next = loop;
        cur = cur->next = new_unary(ND_EXPR_STMT, new_var_node(new, tok), tok);
        Node *node = new_node(ND_STMT_EXPR, tok);
        node->body = head.next;
        return node;
    }
    /// Convert `A op= B` to ``tmp = &A, *tmp = *tmp op B`.
    Obj *var = new_lvar("", pointer_to(binary->lhs->ty));
    Node *expr1 = new_binary(ND_ASSIGN, new_var_node(var, tok),
                             new_unary(ND_ADDR, binary->lhs, tok), tok);
    Node *expr2 =
            new_binary(ND_ASSIGN,
                       new_unary(ND_DEREF, new_var_node(var, tok), tok),
                       new_binary(binary->kind,
                                  new_unary(ND_DEREF, new_var_node(var, tok), tok),
                                  binary->rhs,
                                  tok),
                       tok);
    return new_binary(ND_COMMA, expr1, expr2, tok);
}

/// Parse assignment operators
static Node *assign(Token **rest, Token *tok) {
    Node *node = conditional(&tok, tok);
    if (equal(tok, OP_ASSIGN)) return new_binary(ND_ASSIGN, node, assign(rest, tok->next), tok);
    if (equal(tok, OP_ASSIGN_ADD)) return to_assign(new_add(node, assign(rest, tok->next), tok));
    if (equal(tok, OP_ASSIGN_SUB)) return to_assign(new_sub(node, assign(rest, tok->next), tok));
    if (equal(tok, OP_ASSIGN_MUL))
        return to_assign(new_binary(ND_MUL, node, assign(rest, tok->next), tok));
    if (equal(tok, OP_ASSIGN_DIV))
        return to_assign(new_binary(ND_DIV, node, assign(rest, tok->next), tok));
    if (equal(tok, OP_ASSIGN_MOD))
        return to_assign(new_binary(ND_MOD, node, assign(rest, tok->next), tok));
    if (equal(tok, OP_ASSIGN_AND))
        return to_assign(new_binary(ND_BITAND, node, assign(rest, tok->next), tok));
    if (equal(tok, OP_ASSIGN_OR))
        return to_assign(new_binary(ND_BITOR, node, assign(rest, tok->next), tok));
    if (equal(tok, OP_ASSIGN_XOR))
        return to_assign(new_binary(ND_BITXOR, node, assign(rest, tok->next), tok));
    if (equal(tok, OP_ASSIGN_SHL))
        return to_assign(new_binary(ND_SHL, node, assign(rest, tok->next), tok));
    if (equal(tok, OP_ASSIGN_SHR))
        return to_assign(new_binary(ND_SHR, node, assign(rest, tok->next), tok));
    *rest = tok;
    return node;
}

/// Parse conditional operators
static Node *conditional(Token **rest, Token *tok) {
    Node *cond = logor(&tok, tok);
    if (!equal(tok, PT_QUEST)) {
        *rest = tok;
        return cond;
    }
    if (equal(tok->next, PT_COLON)) {
        add_type(cond);
        Obj *var = new_lvar("", cond->ty);
        Node *lhs = new_binary(ND_ASSIGN, new_var_node(var, tok), cond, tok);
        Node *rhs = new_node(ND_COND, tok);
        rhs->cond = new_var_node(var, tok);
        rhs->then = new_var_node(var, tok);
        rhs->els = conditional(rest, tok->next->next);
        return new_binary(ND_COMMA, lhs, rhs, tok);
    }
    Node *node = new_node(ND_COND, tok);
    node->cond = cond;
    node->then = expr(&tok, tok->next);
    tok = skip(tok, PT_COLON);
    node->els = conditional(rest, tok);
    return node;
}

/// Logic or parsing
static Node *logor(Token **rest, Token *tok) {
    Node *node = logand(&tok, tok);
    while (equal(tok, OP_LOG_OR)) {
        Token *start = tok;
        node = new_binary(ND_LOGOR, node, logand(&tok, tok->next), start);
    }
    *rest = tok;
    return node;
}

/// Logic and parsing
static Node *logand(Token **rest, Token *tok) {
    Node *node = bitor(&tok, tok);
    while (equal(tok, OP_LOG_AND)) {
        Token *start = tok;
        node = new_binary(ND_LOGAND, node, bitor(&tok, tok->next), start);
    }
    *rest = tok;
    return node;
}

/// Bitwise or parsing
static Node *bitor(Token **rest, Token *tok) {
    Node *node = bitxor(&tok, tok);
    while (equal(tok, OP_OR)) {
        Token *start = tok;
        node = new_binary(ND_BITOR, node, bitxor(&tok, tok->next), start);
    }
    *rest = tok;
    return node;
}

/// Bitwise xor parsing
static Node *bitxor(Token **rest, Token *tok) {
    Node *node = bitand(&tok, tok);
    while (equal(tok, OP_XOR)) {
        Token *start = tok;
        node = new_binary(ND_BITXOR, node, bitand(&tok, tok->next), start);
    }
    *rest = tok;
    return node;
}

/// Bitwise and parsing
static Node *bitand(Token **rest, Token *tok) {
    Node *node = equality(&tok, tok);
    while (equal(tok, OP_AND)) {
        Token *start = tok;
        node = new_binary(ND_BITAND, node, equality(&tok, tok->next), start);
    }
    *rest = tok;
    return node;
}

/// Equality operators parsing
static Node *equality(Token **rest, Token *tok) {
    Node *node = relational(&tok, tok);
    for (;;) {
        Token *start = tok;
        if (equal(tok, OP_LOG_EQ)) {
            node = new_binary(ND_EQ, node, relational(&tok, tok->next), start);
            continue;
        }
        if (equal(tok, OP_LOG_NE)) {
            node = new_binary(ND_NE, node, relational(&tok, tok->next), start);
            continue;
        }
        *rest = tok;
        return node;
    }
}

/// Relational operators parsing
static Node *relational(Token **rest, Token *tok) {
    Node *node = shift(&tok, tok);
    for (;;) {
        Token *start = tok;
        if (equal(tok, OP_LOG_LT)) {
            node = new_binary(ND_LT, node, shift(&tok, tok->next), start);
            continue;
        }
        if (equal(tok, OP_LOG_LE)) {
            node = new_binary(ND_LE, node, shift(&tok, tok->next), start);
            continue;
        }
        if (equal(tok, OP_LOG_GT)) {
            node = new_binary(ND_LT, shift(&tok, tok->next), node, start);
            continue;
        }
        if (equal(tok, OP_LOG_GE)) {
            node = new_binary(ND_LE, shift(&tok, tok->next), node, start);
            continue;
        }
        *rest = tok;
        return node;
    }
}

/// Shifting operators parsing
static Node *shift(Token **rest, Token *tok) {
    Node *node = add(&tok, tok);
    for (;;) {
        Token *start = tok;
        if (equal(tok, OP_SHL)) {
            node = new_binary(ND_SHL, node, add(&tok, tok->next), start);
            continue;
        }
        if (equal(tok, OP_SHR)) {
            node = new_binary(ND_SHR, node, add(&tok, tok->next), start);
            continue;
        }
        *rest = tok;
        return node;
    }
}

/// Parse addition operator with the overload for pointers.
/// In C, `+` operator is overloaded to perform the pointer arithmetic.
/// If p is a pointer, p+n adds not n but sizeof(*p)*n to the value of p,
/// so that p+n points to the location n elements (not bytes) ahead of p.
/// In other words, we need to scale an integer value before adding to a
/// pointer value.
static Node *new_add(Node *lhs, Node *rhs, Token *tok) {
    add_type(lhs);
    add_type(rhs);
    /// num + num
    if (is_numeric(lhs->ty) && is_numeric(rhs->ty)) return new_binary(ND_ADD, lhs, rhs, tok);
    if (lhs->ty->base && rhs->ty->base) error_tok(tok, INVALID_OP);
    /// num + ptr to ptr + num
    if (!lhs->ty->base && rhs->ty->base) {
        Node *tmp = lhs;
        lhs = rhs;
        rhs = tmp;
    }
    /// VLA + num
    if (lhs->ty->base->kind == TY_VLA) {
        rhs = new_binary(ND_MUL, rhs, new_var_node(lhs->ty->base->vla_size, tok), tok);
        return new_binary(ND_ADD, lhs, rhs, tok);
    }
    /// ptr + num
    rhs = new_binary(ND_MUL, rhs, new_long(lhs->ty->base->size, tok), tok);
    return new_binary(ND_ADD, lhs, rhs, tok);
}

/// Parse subtraction operator with the overload for pointers.
static Node *new_sub(Node *lhs, Node *rhs, Token *tok) {
    add_type(lhs);
    add_type(rhs);
    /// num - num
    if (is_numeric(lhs->ty) && is_numeric(rhs->ty)) return new_binary(ND_SUB, lhs, rhs, tok);
    /// ptr - num
    if (lhs->ty->base && is_int(rhs->ty)) {
        rhs = new_binary(ND_MUL, rhs, new_long(lhs->ty->base->size, tok), tok);
        add_type(rhs);
        Node *node = new_binary(ND_SUB, lhs, rhs, tok);
        node->ty = lhs->ty;
        return node;
    }
    /// ptr - ptr
    if (lhs->ty->base && rhs->ty->base) {
        Node *node = new_binary(ND_SUB, lhs, rhs, tok);
        node->ty = ty_long;
        return new_binary(ND_DIV, node, new_num(lhs->ty->base->size, tok), tok);
    }
    /// VLA - num
    if (lhs->ty->base->kind == TY_VLA) {
        rhs = new_binary(ND_MUL, rhs, new_var_node(lhs->ty->base->vla_size, tok), tok);
        add_type(rhs);
        Node *node = new_binary(ND_SUB, lhs, rhs, tok);
        node->ty = lhs->ty;
        return node;
    }
    error_tok(tok, INVALID_OP);
}

/// Additive operators parsing
static Node *add(Token **rest, Token *tok) {
    Node *node = mul(&tok, tok);
    for (;;) {
        Token *start = tok;
        if (equal(tok, OP_ADD)) {
            node = new_add(node, mul(&tok, tok->next), start);
            continue;
        }
        if (equal(tok, OP_SUB)) {
            node = new_sub(node, mul(&tok, tok->next), start);
            continue;
        }
        *rest = tok;
        return node;
    }
}

/// Multiplicative operators parsing
static Node *mul(Token **rest, Token *tok) {
    Node *node = cast(&tok, tok);
    for (;;) {
        Token *start = tok;
        if (equal(tok, OP_MUL)) {
            node = new_binary(ND_MUL, node, cast(&tok, tok->next), start);
            continue;
        }
        if (equal(tok, OP_DIV)) {
            node = new_binary(ND_DIV, node, cast(&tok, tok->next), start);
            continue;
        }
        if (equal(tok, OP_MOD)) {
            node = new_binary(ND_MOD, node, cast(&tok, tok->next), start);
            continue;
        }
        *rest = tok;
        return node;
    }
}

/// Casting operation parsing
static Node *cast(Token **rest, Token *tok) {
    if (equal(tok, PT_PAREN_OPEN) && is_typename(tok->next)) {
        Token *start = tok;
        Type *ty = typename(&tok, tok->next);
        tok = skip(tok, PT_PAREN_CLOSE);
        if (equal(tok, PT_BRACE_OPEN)) return unary(rest, start);
        Node *node = new_cast(cast(rest, tok), ty);
        node->tok = tok;
        return node;
    }
    return unary(rest, tok);
}

/// Unary operators èarsing
static Node *unary(Token **rest, Token *tok) {
    if (equal(tok, OP_ADD)) return cast(rest, tok->next);
    if (equal(tok, OP_SUB)) return new_unary(ND_NEG, cast(rest, tok->next), tok);
    if (equal(tok, OP_AND)) {
        Node *lhs = cast(rest, tok->next);
        add_type(lhs);
        if (lhs->kind == ND_MEMBER && lhs->member->is_bitfield) error_tok(tok, CANNOT_ADDR_BITF);
        return new_unary(ND_ADDR, lhs, tok);
    }
    if (equal(tok, OP_MUL)) {
        /// If some is a func, deferencing it should not do anything
        /// Indifference to some, *some, **some, ***some, ...
        Node *node = cast(rest, tok->next);
        add_type(node);
        if (node->ty->kind == TY_FUNC) return node;
        return new_unary(ND_DEREF, node, tok);
    }
    if (equal(tok, OP_LOG_NOT)) return new_unary(ND_NOT, cast(rest, tok->next), tok);
    if (equal(tok, OP_NOT)) return new_unary(ND_BITNOT, cast(rest, tok->next), tok);
    if (equal(tok, OP_INCR))
        return to_assign(new_add(unary(rest, tok->next), new_num(1, tok), tok));
    if (equal(tok, OP_DECR))
        return to_assign(new_sub(unary(rest, tok->next), new_num(1, tok), tok));
    if (equal(tok, OP_LOG_AND)) {
        Node *node = new_node(ND_LABEL_VAL, tok);
        node->label = get_ident(tok->next);
        node->goto_next = gotos;
        gotos = node;
        *rest = tok->next->next;
        return node;
    }
    return postfix(rest, tok);
}

/// Parse struct members
static void struct_members(Token **rest, Token *tok, Type *ty) {
    Member head = {};
    Member *cur = &head;
    int idx = 0;
    while (!equal(tok, PT_BRACE_CLOSE)) {
        VarAttr attr = {};
        Type *basety = declspec(&tok, tok, &attr);
        bool first = true;
        /// Anonymous struct member
        if ((basety->kind == TY_STRUCT || basety->kind == TY_UNION) &&
            consume(&tok, tok, PT_SEMICOLON)) {
            Member *mem = calloc(1, sizeof(Member));
            mem->ty = basety;
            mem->idx = idx++;
            mem->align = attr.align ? attr.align : mem->ty->align;
            cur = cur->next = mem;
            continue;
        }
        /// Regular struct members
        while (!consume(&tok, tok, PT_SEMICOLON)) {
            if (!first) tok = skip(tok, PT_COMMA);
            first = false;
            Member *mem = calloc(1, sizeof(Member));
            mem->ty = declarator(&tok, tok, basety);
            mem->name = mem->ty->name;
            mem->idx = idx++;
            mem->align = attr.align ? attr.align : mem->ty->align;
            if (consume(&tok, tok, PT_COLON)) {
                mem->is_bitfield = true;
                mem->bit_width = const_expr(&tok, tok);
            }
            cur = cur->next = mem;
        }
    }
    /// If the last element is an array of incomplete type, it's
    /// called a "flexible array member". It should behave as if
    /// it were a zero-sized array.
    if (cur != &head && cur->ty->kind == TY_ARRAY && cur->ty->array_len < 0) {
        cur->ty = array_of(cur->ty->base, 0);
        ty->is_flexible = true;
    }
    *rest = tok->next;
    ty->members = head.next;
}

/// Parse attribute list
static Token *attribute_list(Token *tok, Type *ty) {
    while (consume(&tok, tok, PP_ATTRIBUTE)) {
        tok = skip(tok, PT_PAREN_OPEN);
        tok = skip(tok, PT_PAREN_OPEN);
        bool first = true;

        while (!consume(&tok, tok, PT_PAREN_CLOSE)) {
            if (!first) tok = skip(tok, PT_COMMA);
            first = false;
            if (consume(&tok, tok, PP_PACKED)) {
                ty->is_packed = true;
                continue;
            }
            if (consume(&tok, tok, PP_ALINGED)) {
                tok = skip(tok, PT_PAREN_OPEN);
                ty->align = const_expr(&tok, tok);
                tok = skip(tok, PT_PAREN_CLOSE);
                continue;
            }
            error_tok(tok, UNKNOWN_ATTR);
        }
        tok = skip(tok, PT_PAREN_CLOSE);
    }
    return tok;
}

/// Parse struct/union declaration
static Type *struct_union_decl(Token **rest, Token *tok) {
    Type *ty = struct_type();
    tok = attribute_list(tok, ty);
    /// Read a tag.
    Token *tag = NULL;
    if (tok->kind == TK_IDENT) {
        tag = tok;
        tok = tok->next;
    }
    if (tag && !equal(tok, PT_BRACE_OPEN)) {
        *rest = tok;
        Type *ty2 = find_tag(tag);
        if (ty2) return ty2;
        ty->size = -1;
        push_tag_scope(tag, ty);
        return ty;
    }
    tok = skip(tok, PT_BRACE_OPEN);
    /// Construct a struct object.
    struct_members(&tok, tok, ty);
    *rest = attribute_list(tok, ty);
    if (tag) {
        /// If this is a redefinition, overwrite a previous type.
        /// Otherwise, register the struct type.
        Type *ty2 = hashmap_get_wlen(&scope->tags, tag->loc, tag->len);
        if (ty2) {
            *ty2 = *ty;
            return ty2;
        }
        push_tag_scope(tag, ty);
    }
    return ty;
}

/// Parse struct declaration
static Type *struct_decl(Token **rest, Token *tok) {
    Type *ty = struct_union_decl(rest, tok);
    ty->kind = TY_STRUCT;
    if (ty->size < 0) return ty;
    /// Assign offsets within the struct to members.
    int bits = 0;
    for (Member *mem = ty->members; mem; mem = mem->next) {
        if (mem->is_bitfield && mem->bit_width == 0) {
            /// Zero-width anonymous bitfield has a special meaning.
            /// It affects only alignment.
            bits = align_to(bits, mem->ty->size * 8);
        } else if (mem->is_bitfield) {
            int sz = mem->ty->size;
            if (bits / (sz * 8) != (bits + mem->bit_width - 1) / (sz * 8)) bits = align_to(bits, sz * 8);
            mem->offs = align_down(bits / 8, sz);
            mem->bit_offs = bits % (sz * 8);
            bits += mem->bit_width;
        } else {
            if (!ty->is_packed) bits = align_to(bits, mem->align * 8);
            mem->offs = bits / 8;
            bits += mem->ty->size * 8;
        }
        if (!ty->is_packed && ty->align < mem->align) ty->align = mem->align;
    }
    ty->size = align_to(bits, ty->align * 8) / 8;
    return ty;
}

/// union-decl = struct-union-decl
static Type *union_decl(Token **rest, Token *tok) {
    Type *ty = struct_union_decl(rest, tok);
    ty->kind = TY_UNION;
    if (ty->size < 0) return ty;
    /// If union, we don't have to assign offsets because they
    /// are already initialized to zero. We need to compute the
    /// alignment and the size though.
    for (Member *mem = ty->members; mem; mem = mem->next) {
        if (ty->align < mem->align) ty->align = mem->align;
        if (ty->size < mem->ty->size) ty->size = mem->ty->size;
    }
    ty->size = align_to(ty->size, ty->align);
    return ty;
}

/// Find a struct member by name.
static Member *get_struct_member(Type *ty, Token *tok) {
    for (Member *mem = ty->members; mem; mem = mem->next) {
        /// Anonymous struct member
        if ((mem->ty->kind == TY_STRUCT || mem->ty->kind == TY_UNION) && !mem->name) {
            if (get_struct_member(mem->ty, tok)) return mem;
            continue;
        }
        /// Regular struct member
        if (mem->name->len == tok->len && !strncmp(mem->name->loc, tok->loc, tok->len)) return mem;
    }
    return NULL;
}

/// Anonymous struct members parsing.
/// Create a node representing a struct member access, such as some.other
/// where some is a struct and other is a member name.
///
/// C has a feature called "anonymous struct" which allows a struct to
/// have another unnamed struct as a member like this:
///
///   struct { struct { int a; }; int b; } x;
///
/// The members of an anonymous struct belong to the outer struct's
/// member namespace. Therefore, in the above example, you can access
/// member "a" of the anonymous struct as "x.a".
static Node *struct_ref(Node *node, Token *tok) {
    add_type(node);
    if (node->ty->kind != TY_STRUCT && node->ty->kind != TY_UNION)
        error_tok(node->tok, NO_STRUCT_UNION);
    Type *ty = node->ty;
    for (;;) {
        Member *mem = get_struct_member(ty, tok);
        if (!mem) error_tok(tok, NO_SUCH_MEMBER2);
        node = new_unary(ND_MEMBER, node, tok);
        node->member = mem;
        if (mem->name) break;
        ty = mem->ty;
    }
    return node;
}

/// Convert A++ to `(typeof A)((A += 1) - 1)`
static Node *new_inc_dec(Node *node, Token *tok, int addend) {
    add_type(node);
    return new_cast(new_add(to_assign(new_add(node, new_num(addend, tok), tok)),
                            new_num(-addend, tok), tok), node->ty);
}

/// Postfix operators parsing
static Node *postfix(Token **rest, Token *tok) {
    if (equal(tok, PT_PAREN_OPEN) && is_typename(tok->next)) {
        /// Compound literal
        Token *start = tok;
        Type *ty = typename(&tok, tok->next);
        tok = skip(tok, PT_PAREN_CLOSE);
        if (scope->next == NULL) {
            Obj *var = new_anon_gvar(ty);
            gvar_initializer(rest, tok, var);
            return new_var_node(var, start);
        }
        Obj *var = new_lvar("", ty);
        Node *lhs = lvar_initializer(rest, tok, var);
        Node *rhs = new_var_node(var, tok);
        return new_binary(ND_COMMA, lhs, rhs, start);
    }
    Node *node = primary(&tok, tok);
    for (;;) {
        if (equal(tok, PT_PAREN_OPEN)) {
            node = funcall(&tok, tok->next, node);
            continue;
        }
        if (equal(tok, PT_BRACKET_OPEN)) {
            /// x[y] is short for *(x+y)
            Token *start = tok;
            Node *idx = expr(&tok, tok->next);
            tok = skip(tok, PT_BRACKET_CLOSE);
            node = new_unary(ND_DEREF, new_add(node, idx, start), start);
            continue;
        }
        if (equal(tok, PT_POINT)) {
            node = struct_ref(node, tok->next);
            tok = tok->next->next;
            continue;
        }
        if (equal(tok, PT_ARROW)) {
            /// x->y is short for (*x).y
            node = new_unary(ND_DEREF, node, tok);
            node = struct_ref(node, tok->next);
            tok = tok->next->next;
            continue;
        }
        if (equal(tok, OP_INCR)) {
            node = new_inc_dec(node, tok, 1);
            tok = tok->next;
            continue;
        }
        if (equal(tok, OP_DECR)) {
            node = new_inc_dec(node, tok, -1);
            tok = tok->next;
            continue;
        }
        *rest = tok;
        return node;
    }
}

/// Function call parsing
static Node *funcall(Token **rest, Token *tok, Node *fn) {
    add_type(fn);
    if (fn->ty->kind != TY_FUNC && (fn->ty->kind != TY_PTR || fn->ty->base->kind != TY_FUNC))
        error_tok(fn->tok, NOT_FUNC);
    Type *ty = (fn->ty->kind == TY_FUNC) ? fn->ty : fn->ty->base;
    Type *param_ty = ty->params;
    Node head = {};
    Node *cur = &head;
    while (!equal(tok, PT_PAREN_CLOSE)) {
        if (cur != &head) tok = skip(tok, PT_COMMA);
        Node *arg = assign(&tok, tok);
        add_type(arg);
        if (!param_ty && !ty->is_variadic) error_tok(tok, TOO_MANY_ARGUMENTS);
        if (param_ty) {
            if (param_ty->kind != TY_STRUCT && param_ty->kind != TY_UNION) arg = new_cast(arg, param_ty);
            param_ty = param_ty->next;
        } else if (arg->ty->kind == TY_FLOAT) {
            /// If parameter type is omitted (e.g. in "..."), float
            /// arguments are promoted to double.
            arg = new_cast(arg, ty_double);
        }
        cur = cur->next = arg;
    }
    if (param_ty) error_tok(tok, TOO_FEW_ARGUMENTS);
    *rest = skip(tok, PT_PAREN_CLOSE);
    Node *node = new_unary(ND_FUNCALL, fn, tok);
    node->func_ty = ty;
    node->ty = ty->return_ty;
    node->args = head.next;
    /// If a function returns a struct, it is caller's responsibility
    /// to allocate a space for the return value.
    if (node->ty->kind == TY_STRUCT || node->ty->kind == TY_UNION) node->ret_buffer = new_lvar("", node->ty);
    return node;
}

/// Parsing for generic selections
static Node *generic_selection(Token **rest, Token *tok) {
    Token *start = tok;
    tok = skip(tok, PT_PAREN_OPEN);
    Node *ctrl = assign(&tok, tok);
    add_type(ctrl);
    Type *t1 = ctrl->ty;
    if (t1->kind == TY_FUNC) t1 = pointer_to(t1);
    else if (t1->kind == TY_ARRAY) t1 = pointer_to(t1->base);
    Node *ret = NULL;
    while (!consume(rest, tok, PT_PAREN_CLOSE)) {
        tok = skip(tok, PT_COMMA);
        if (equal(tok, KW_DEFAULT)) {
            tok = skip(tok->next, PT_COLON);
            Node *node = assign(&tok, tok);
            if (!ret) ret = node;
            continue;
        }
        Type *t2 = typename(&tok, tok);
        tok = skip(tok, PT_COLON);
        Node *node = assign(&tok, tok);
        if (is_compatible(t1, t2)) ret = node;
    }

    if (!ret) error_tok(start, CTRL_EXPR_TYPE_NC);
    return ret;
}

/// Parsing for primary expressions
static Node *primary(Token **rest, Token *tok) {
    Token *start = tok;
    if (equal(tok, PT_PAREN_OPEN) && equal(tok->next, PT_BRACE_OPEN)) {
        /// This is a GNU statement expresssion.
        Node *node = new_node(ND_STMT_EXPR, tok);
        node->body = compound_stmt(&tok, tok->next->next)->body;
        *rest = skip(tok, PT_PAREN_CLOSE);
        return node;
    }
    if (equal(tok, PT_PAREN_OPEN)) {
        Node *node = expr(&tok, tok->next);
        *rest = skip(tok, PT_PAREN_CLOSE);
        return node;
    }
    if (equal(tok, KW_SIZEOF) && equal(tok->next, PT_PAREN_OPEN) && is_typename(tok->next->next)) {
        Type *ty = typename(&tok, tok->next->next);
        *rest = skip(tok, PT_PAREN_CLOSE);

        if (ty->kind == TY_VLA) {
            if (ty->vla_size) return new_var_node(ty->vla_size, tok);
            Node *lhs = compute_vla_size(ty, tok);
            Node *rhs = new_var_node(ty->vla_size, tok);
            return new_binary(ND_COMMA, lhs, rhs, tok);
        }
        return new_ulong(ty->size, start);
    }
    if (equal(tok, KW_SIZEOF)) {
        Node *node = unary(rest, tok->next);
        add_type(node);
        if (node->ty->kind == TY_VLA) return new_var_node(node->ty->vla_size, tok);
        return new_ulong(node->ty->size, tok);
    }
    if (equal(tok, PP_ALIGNOF) && equal(tok->next, PT_PAREN_OPEN) && is_typename(tok->next->next)) {
        Type *ty = typename(&tok, tok->next->next);
        *rest = skip(tok, PT_PAREN_CLOSE);
        return new_ulong(ty->align, tok);
    }
    if (equal(tok, PP_ALIGNOF)) {
        Node *node = unary(rest, tok->next);
        add_type(node);
        return new_ulong(node->ty->align, tok);
    }
    if (equal(tok, PP_GENERIC)) return generic_selection(rest, tok->next);
    // TODO: FIND OUT WHAT THIS IS
    if (equal(tok, "__builtin_types_compatible_p")) {
        tok = skip(tok->next, PT_PAREN_OPEN);
        Type *t1 = typename(&tok, tok);
        tok = skip(tok, PT_COMMA);
        Type *t2 = typename(&tok, tok);
        *rest = skip(tok, PT_PAREN_CLOSE);
        return new_num(is_compatible(t1, t2), start);
    }
    if (equal(tok, "__builtin_reg_class")) {
        tok = skip(tok->next, PT_PAREN_OPEN);
        Type *ty = typename(&tok, tok);
        *rest = skip(tok, PT_PAREN_CLOSE);
        if (is_int(ty) || ty->kind == TY_PTR) return new_num(0, start);
        if (is_flonum(ty)) return new_num(1, start);
        return new_num(2, start);
    }
    if (equal(tok, "__builtin_compare_and_swap")) {
        Node *node = new_node(ND_CAS, tok);
        tok = skip(tok->next, PT_PAREN_OPEN);
        node->cas_addr = assign(&tok, tok);
        tok = skip(tok, PT_COMMA);
        node->cas_old = assign(&tok, tok);
        tok = skip(tok, PT_COMMA);
        node->cas_new = assign(&tok, tok);
        *rest = skip(tok, PT_PAREN_CLOSE);
        return node;
    }
    if (equal(tok, "__builtin_atomic_exchange")) {
        Node *node = new_node(ND_EXCH, tok);
        tok = skip(tok->next, PT_PAREN_OPEN);
        node->lhs = assign(&tok, tok);
        tok = skip(tok, PT_COMMA);
        node->rhs = assign(&tok, tok);
        *rest = skip(tok, PT_PAREN_CLOSE);
        return node;
    }
    // END TODO
    if (tok->kind == TK_IDENT) {
        /// Variable or enum constant
        VarScope *sc = find_var(tok);
        *rest = tok->next;

        /// For "static inline" function
        if (sc && sc->var && sc->var->is_function) {
            if (current_fn) strarray_push(&current_fn->refs, sc->var->name);
            else sc->var->is_root = true;
        }
        if (sc) {
            if (sc->var) return new_var_node(sc->var, tok);
            if (sc->enum_ty) return new_num(sc->enum_val, tok);
        }
        if (equal(tok->next, PT_PAREN_OPEN)) error_tok(tok, IMPLICIT_DECL);
        error_tok(tok, UNDEF_VAR);
    }
    if (tok->kind == TK_STR) {
        Obj *var = new_string_literal(tok->str, tok->ty);
        *rest = tok->next;
        return new_var_node(var, tok);
    }
    if (tok->kind == TK_NUM) {
        Node *node;
        if (is_flonum(tok->ty)) {
            node = new_node(ND_NUM, tok);
            node->fval = tok->fval;
        } else {
            node = new_num(tok->val, tok);
        }
        node->ty = tok->ty;
        *rest = tok->next;
        return node;
    }
    error_tok(tok, EXPECTED_EXPR);
}

/// Typedef parsing
static Token *parse_typedef(Token *tok, Type *basety) {
    bool first = true;
    while (!consume(&tok, tok, PT_SEMICOLON)) {
        if (!first) tok = skip(tok, PT_COMMA);
        first = false;
        Type *ty = declarator(&tok, tok, basety);
        if (!ty->name) error_tok(ty->name_pos, ALIAS_NAME_OMITTED);
        push_scope(get_ident(ty->name))->type_def = ty;
    }
    return tok;
}

/// Creates lvars for parameters
static void create_param_lvars(Type *param) {
    if (param) {
        create_param_lvars(param->next);
        if (!param->name) error_tok(param->name_pos, PARAM_NAME_OMITTED);
        new_lvar(get_ident(param->name), param);
    }
}

/// This function matches gotos or labels-as-values with labels.
///
/// We cannot resolve gotos as we parse a function because gotos
/// can refer a label that appears later in the function.
/// So, we need to do this after we parse the entire function.
static void resolve_goto_labels(void) {
    for (Node *x = gotos; x; x = x->goto_next) {
        for (Node *y = labels; y; y = y->goto_next) {
            if (!strcmp(x->label, y->label)) {
                x->unique_label = y->unique_label;
                break;
            }
        }
        if (x->unique_label == NULL) error_tok(x->tok->next, USE_UNDECL_LABEL);
    }
    gotos = labels = NULL;
}

/// Find a function by name
static Obj *find_func(char *name) {
    Scope *sc = scope;
    while (sc->next) sc = sc->next;
    VarScope *sc2 = hashmap_get(&sc->vars, name);
    if (sc2 && sc2->var && sc2->var->is_function) return sc2->var;
    return NULL;
}

/// Mark a function as live
static void mark_live(Obj *var) {
    if (!var->is_function || var->is_live) return;
    var->is_live = true;
    for (int i = 0; i < var->refs.len; i++) {
        Obj *fn = find_func(var->refs.data[i]);
        if (fn) mark_live(fn);
    }
}

/// Parse a function
static Token *function(Token *tok, Type *basety, VarAttr *attr) {
    Type *ty = declarator(&tok, tok, basety);
    if (!ty->name) error_tok(ty->name_pos, FUNC_NAME_OMITTED);
    char *name_str = get_ident(ty->name);
    Obj *fn = find_func(name_str);
    if (fn) {
        /// Redeclaration
        if (!fn->is_function) error_tok(tok, REDECL_FUNC);
        if (fn->is_definition && equal(tok, PT_BRACE_OPEN)) error_tok(tok, REDEF_FUNC, name_str);
        if (!fn->is_static && attr->is_static) error_tok(tok, STATIC_NONSTATIC);
        fn->is_definition = fn->is_definition || equal(tok, PT_BRACE_OPEN);
    } else {
        fn = new_gvar(name_str, ty);
        fn->is_function = true;
        fn->is_definition = equal(tok, PT_BRACE_OPEN);
        fn->is_static = attr->is_static || (attr->is_inline && !attr->is_extern);
        fn->is_inline = attr->is_inline;
    }
    fn->is_root = !(fn->is_static && fn->is_inline);
    if (consume(&tok, tok, PT_SEMICOLON)) return tok;
    current_fn = fn;
    locals = NULL;
    enter_scope();
    create_param_lvars(ty->params);
    /// A buffer for a struct/union return value is passed
    /// as the hidden first parameter.
    Type *rty = ty->return_ty;
    if ((rty->kind == TY_STRUCT || rty->kind == TY_UNION) && rty->size > 16)
        new_lvar("", pointer_to(rty));
    fn->params = locals;
    if (ty->is_variadic)
        fn->va_area = new_lvar(PP_VAREA, array_of(ty_char, 136));
    fn->alloca_bottom = new_lvar(PP_ALLOC_SIZE, pointer_to(ty_char));
    tok = skip(tok, PT_BRACE_OPEN);
    /// [https:///www.sigbus.info/n1570#6.4.2.2p1] "__func__" is
    /// automatically defined as a local variable containing the
    /// current function name.
    push_scope(PP_FUNCTION)->var =
            new_string_literal(fn->name, array_of(ty_char, strlen(fn->name) + 1));
    fn->body = compound_stmt(&tok, tok);
    fn->locals = locals;
    leave_scope();
    resolve_goto_labels();
    return tok;
}

/// Parse a global variable
static Token *global_variable(Token *tok, Type *basety, VarAttr *attr) {
    bool first = true;
    while (!consume(&tok, tok, PT_SEMICOLON)) {
        if (!first) tok = skip(tok, PT_COMMA);
        first = false;
        Type *ty = declarator(&tok, tok, basety);
        if (!ty->name) error_tok(ty->name_pos, MISSING_VARNAME);
        Obj *var = new_gvar(get_ident(ty->name), ty);
        var->is_definition = !attr->is_extern;
        var->is_static = attr->is_static;
        var->is_tls = attr->is_tls;
        if (attr->align) var->align = attr->align;
        if (equal(tok, OP_ASSIGN)) gvar_initializer(&tok, tok->next, var);
        else if (!attr->is_extern && !attr->is_tls) var->is_tentative = true;
    }
    return tok;
}

/// Lookahead tokens and returns true if a given token is a start
/// of a function definition or declaration.
static bool is_function(Token *tok) {
    if (equal(tok, PT_SEMICOLON)) return false;
    Type dummy = {};
    Type *ty = declarator(&tok, tok, &dummy);
    return ty->kind == TY_FUNC;
}

/// Remove redundant tentative definitions.
static void scan_globals(void) {
    Obj head;
    Obj *cur = &head;
    for (Obj *var = globals; var; var = var->next) {
        if (!var->is_tentative) {
            cur = cur->next = var;
            continue;
        }
        /// Find another definition of the same identifier.
        Obj *var2 = globals;
        for (; var2; var2 = var2->next)
            if (var != var2 && var2->is_definition && !strcmp(var->name, var2->name)) break;
        /// If there's another definition, the tentative definition
        /// is redundant
        if (!var2) cur = cur->next = var;
    }
    cur->next = NULL;
    globals = head.next;
}

/// Declare builtin functions
static void declare_builtin_functions(void) {
    Type *ty = func_type(pointer_to(ty_void));
    ty->params = copy_type(ty_int);
    builtin_alloca = new_gvar(PP_ALLOCA, ty);
    builtin_alloca->is_definition = false;
}

/// Parses a program
Obj *parse(Token *tok) {
    declare_builtin_functions();
    globals = NULL;
    while (tok->kind != TK_EOF) {
        VarAttr attr = {};
        Type *basety = declspec(&tok, tok, &attr);
        /// Typedef
        if (attr.is_typedef) {
            tok = parse_typedef(tok, basety);
            continue;
        }
        /// Function
        if (is_function(tok)) {
            tok = function(tok, basety, &attr);
            continue;
        }
        /// Global variable
        tok = global_variable(tok, basety, &attr);
    }
    for (Obj *var = globals; var; var = var->next) if (var->is_root) mark_live(var);
    /// Remove redundant tentative definitions.
    scan_globals();
    return globals;
}