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
// TODO: Substitute C with ace characteristics

#include <assert.h>
#include <ctype.h>
#include <errno.h>
#include <glob.h>
#include <libgen.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdnoreturn.h>
#include <string.h>
#include <strings.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

// Max value expression
#define MAX(x, y) ((x) > (y) ? (x) : (y))

// Min value expression
#define MIN(x, y) ((x) < (y) ? (x) : (y))

// If the compiler does not support GNU extensions
// __attribute__(x) is defined
#ifndef __GNUC__
#define __attribute__(x)
#endif

// Structure `Type` type definition
typedef struct Type Type;

// Structure `Node` type definition
typedef struct Node Node;

// Structure `Member` type definition
typedef struct Member Member;

// Structure `Relocation` type definition
typedef struct Relocation Relocation;

// Structure `Hideset` type definition
typedef struct Hideset Hideset;

//
// str.c
//

// Structure `StringArray` type definition
typedef struct {
    char **data;
    int capacity;
    int len;
} StringArray;

// Pushes a string to a `StringArray?
void strarray_push(StringArray *array, char *s);

// Returns a formatted string given a format and arguments
char *format(char *fmt, ...) __attribute__((format(printf,1,2)));

//
// tok.c
//

// Enum defining token kinds
typedef enum {
    TK_IDENT,   // Identifiers
    TK_PUNCT,   // Punctuators
    TK_KEYWORD, // Keywords
    TK_STR,     // String literals
    TK_NUM,     // Numeric literals
    TK_PP_NUM,  // Preprocessor numeric literals
    TK_EOF      // End of file markers
} TokenKind;

// Structure `File` type definition
typedef struct {
    char *name;         // File name
    int file_no;        // File number
    char *contents;     // File contents
    char *display_name; // Display name
    int line_delta;     // Number of lines
} File;

// Structure `Token` type definition
typedef struct Token Token;

// Structure defining a `Token`.
struct Token {
    TokenKind kind;     // Token Kind
    Token *next;        // Next token
    int64_t val;        // If kind is TK_NUM, a value
    long double fval;   // If kind is TK_NUM, a value
    char *loc;          // Token location
    int len;            // Token length
    Type *ty;           // Only if TK_NUM or TK_STR
    char *str;          // String literal content with '\0' termination
    File *file;         // Source location
    char *filename;     // Filename
    int line_no;        // Line num
    int line_delta;     // Line num
    bool at_sol;       // True if token is line start
    bool has_space;     // True if token follows space
    Hideset *hideset;   // Macro expansion
    Token *origin;      // Original token for macro expansion
};

// Prints a formatted error given a format string
noreturn void error(char *fmt, ...) __attribute__((format(printf,1,2)));

// Prints a formatted error at `loc` given a format string and location
noreturn void error_at(char *loc, char *fmt, ...) __attribute__((format(printf,2,3)));

// Prints a formatted error at `tok` given a format string and a token
noreturn void error_tok(Token *tok, char *fmt, ...) __attribute__((format(printf,2,3)));

// Prints a formatted warning at `loc` given a format string and token
void warn_tok(Token *tok, char *fmt, ...) __attribute__((format(printf,2,3)));

// Returns true if `tok` is equal to `op`
bool equal(Token *tok, char *op);

// Skips the token if it is equal to `op`, returns the next token
Token *skip(Token *tok, char *op);

// Consumes the token if it is equal to `str`, returns if the token was consumed
bool consume(Token **rest, Token *tok, char *str);

// Converts preprocessor tokens
void convert_pp_tokens(Token *tok);

// Returns the input files
File **get_input_files(void);

// Returns a new file
File *new_file(char *name, int file_no, char *contents);

// Tokenizes a string literal
Token *tokenize_string_literal(Token *tok, Type *basety);

// Tokenizes a file
Token *tokenize(File *file);

// Tokenizes a file given the filename
Token *tokenize_file(char *filename);

// Unreachable statement error definition
#define unreachable() \
    error("Internal error at %s:%d", __FILE__, __LINE__);

//
// preproc.c
//

// Searches include paths in file, given the filename
char *search_include_paths(char *filename);

// Initializes defined macros
void init_macros(void);

// Defines a macro
void define_macro(char *name, char *buf);

// Undefines a macro
void undefine_macro(char *name);

// Preprocesses a token
Token *preprocess(Token *tok);

//
// parse.c
//

// Defines an object type structure
// Used for global variables and functions
typedef struct Obj Obj;

// Relocation type definition.
// A global var can be defined as const expression
// or ptr to another global var. This is the ptr case,
// so the relocation of the value of a var to another
// var.
typedef struct Relocation Relocation;

// AST (Abstract Syntax Tree) Node type definition.
typedef enum {
    ND_NULL_EXPR, // Do nothing
    ND_ADD,       // +
    ND_SUB,       // -
    ND_MUL,       // *
    ND_DIV,       // /
    ND_NEG,       // unary -
    ND_MOD,       // %
    ND_BITAND,    // &
    ND_BITOR,     // |
    ND_BITXOR,    // ^
    ND_SHL,       // <<
    ND_SHR,       // >>
    ND_EQ,        // ==
    ND_NE,        // !=
    ND_LT,        // <
    ND_LE,        // <=
    ND_ASSIGN,    // =
    ND_COND,      // ?:
    ND_COMMA,     // ,
    ND_MEMBER,    // . (struct member access)
    ND_ADDR,      // unary &
    ND_DEREF,     // unary *
    ND_NOT,       // !
    ND_BITNOT,    // ~
    ND_LOGAND,    // &&
    ND_LOGOR,     // ||
    ND_RETURN,    // "yield"
    ND_IF,        // "if"
    ND_FOR,       // "for" or "while"
    ND_DO,        // "do"
    ND_SWITCH,    // "switch"
    ND_CASE,      // "case"
    ND_BLOCK,     // { ... }
    ND_LABEL,     // Labeled statement
    ND_LABEL_VAL, // [GNU] Labels-as-values
    ND_FUNCALL,   // Function call
    ND_EXPR_STMT, // Expression statement
    ND_STMT_EXPR, // Statement expression
    ND_VAR,       // Variable
    ND_VLA_PTR,   // VLA designator
    ND_NUM,       // Integer
    ND_CAST,      // Type cast
    ND_MEMZERO,   // Zero-clear a stack variable
    ND_ASM,       // "asm"
    ND_CAS,       // Atomic compare-and-swap
    ND_EXCH,      // Atomic exchange
    ND_GOTO,      // "goto"
    ND_GOTO_EXPR // Goto expression
} NodeKind;

// Structure defining an object
struct Obj {
    Obj *next;     // Next object
    char *name;    // Variable name
    Type *ty;      // Type
    Token *tok;    // representative token
    bool is_local; // local or global/function
    int align;     // alignment
    // Local variable
    int offset;
    // Global variable or function
    bool is_function;
    bool is_definition;
    bool is_static;
    // Global variable
    bool is_tentative;
    bool is_tls;
    char *init_data;
    Relocation *rel;
    // Function
    bool is_inline;
    Obj *params;
    Node *body;
    Obj *locals;
    Obj *va_area;
    Obj *alloca_bottom;
    int stack_size;
    // Static inline function
    bool is_live;
    bool is_root;
    StringArray refs;
};

// Relocation definition
struct Relocation {
    Relocation *next;   // Next relocation
    int offset;         // Offset of the relocation
    char **label;       // Label of the relocation
    long addend;        // Addend
};

// AST (Abstract Syntax Tree) node definition.
struct Node {
    NodeKind kind; // Node kind
    Node *next;    // Next node
    Type *ty;      // Type, e.g. int or pointer to int
    Token *tok;    // Representative token
    Node *lhs;     // Left-hand side
    Node *rhs;     // Right-hand side
    // "if" or "for" statement
    Node *cond;
    Node *then;
    Node *els;
    Node *init;
    Node *inc;
    // "break" and "continue" labels
    char *brk_label;
    char *cont_label;
    // Block or statement expression
    Node *body;
    // Struct member access
    Member *member;
    // Function call
    Type *func_ty;
    Node *args;
    bool pass_by_stack;
    Obj *ret_buffer;
    // Goto or labeled statement, or labels-as-values
    char *label;
    char *unique_label;
    Node *goto_next;
    // Switch
    Node *case_next;
    Node *default_case;
    // Case
    long begin;
    long end;
    // "asm" string literal
    char *asm_str;
    // Atomic compare-and-swap
    Node *cas_addr;
    Node *cas_old;
    Node *cas_new;
    // Atomic op= operators
    Obj *atomic_addr;
    Node *atomic_expr;
    // Variable
    Obj *var;
    // Numeric literal
    int64_t val;
    long double fval;
};

// Cast an expression to type
Node *new_cast(Node *expr, Type *ty);

// Constant expression evaluation
int64_t const_expr(Token **rest, Token *tok);

// Parse a token stream
Obj *parse(Token *tok);

//
// type.c
//

// Enum defining type kinds
typedef enum {
    TY_VOID,
    TY_BOOL,
    TY_CHAR,
    TY_SHORT,
    TY_INT,
    TY_LONG,
    TY_FLOAT,
    TY_DOUBLE,
    TY_LDOUBLE,
    TY_ENUM,
    TY_PTR,
    TY_FUNC,
    TY_ARRAY,
    TY_VLA, // variable-length array
    TY_STRUCT,
    TY_UNION,
} TypeKind;

// Structure defining a type.
struct Type {
    TypeKind kind;
    int size;           // Size in bytes
    int align;          // Alignment in bytes
    bool is_unsigned;   // unsigned or signed
    bool is_atomic;     // true if atomic
    Type *origin;       // type comp check
    Type *base;
    // Declaration
    Token *name;
    Token *name_pos;
    // Array
    int array_len;
    // Vectors
    Node *vla_len; // # of elems
    Obj *vla_size; // size of each elem
    // Struct
    Member *members;
    bool is_flexible;
    bool is_packed;
    // Function type
    Type *return_ty;
    Type *params;
    bool is_variadic;
    Type *next;
};

// Structure defining a struct member.
struct Member {
    Member *next;
    Type *ty;
    Token *tok;
    Token *name;
    int idx;
    int align;
    int offs;
    // Bitfield
    bool is_bitfield;
    int bit_offs;
    int bit_width;
};

// Void type definition
extern Type *ty_void;

// Boolean type definition
extern Type *ty_bool;

// Char type definition
extern Type *ty_char;

// Short type definition
extern Type *ty_short;

// Int type definition
extern Type *ty_int;

// Long type definition
extern Type *ty_long;

// Unsigned char type definition
extern Type *ty_uchar;

// Unsigned short type definition
extern Type *ty_ushort;

// Unsigned int type definition
extern Type *ty_uint;

// Unsigned long type definition
extern Type *ty_ulong;

// Float type definition
extern Type *ty_float;

// Double type definition
extern Type *ty_double;

// Long double type definition
extern Type *ty_ldouble;

// Returns true if `ty` is an integer type
bool is_int(Type *ty);

// Returns true if `ty` is a floating point type
bool is_flonum(Type *ty);

// Returns true if `ty` is a numeric type
bool is_numeric(Type *ty);

// Returns true if `t1` and `t2` are compatible
bool is_compatible(Type *t1, Type *t2);

// Copy a type
Type *copy_type(Type *ty);

// Returns the pointing-to type of type `base`
Type *pointer_to(Type *base);

// Returns the function type of function returning `return_ty`
Type *func_type(Type *return_ty);

// Returns the array type of array of `base` and `size`
Type *array_of(Type *base, int size);

// Returns the vector type of vector of `base` and `expr`
Type *is_vla_of(Type *base, Node *expr);

// Returns the type of struct
Type *struct_type(void);

// Returns the type of enum
Type *enum_type(void);

// Adds a type to the type table
void add_type(Node *node);

//
// codegen.c
//

// Generates ASM code given a program and a target file
void codegen(Obj *prog, FILE *out);

// Align `n` to `align` bitwise
int align_to(int n, int align);

//
// utf.c
//

// Returns the utf8 codepoint of `c`
int encode_utf8(char *buf, uint32_t c);

// Returns the decoded codepoint of `p`
uint32_t decode_utf8(char **new_pos, char *p);

// Returns true if `c` is an identifier character
bool is_id1(uint32_t c);
bool is_id2(uint32_t c);

// Returns the display width of `p`
int display_width(char *p, int len);

//
// hashmap.c
//

// Hash entry type definition
typedef struct {
    char *key;
    int keylen;
    void *val;
} HashEntry;

// Hash map type definition
typedef struct {
    HashEntry *buckets;
    int capacity;
    int used;
} HashMap;

// Get entry in hashmap given a hashmap and a key
void *hashmap_get(HashMap *map, char *key);

// Get entry in hashmap given a hashmap, a key and key length
void *hashmap_get_wlen(HashMap *map, char *key, int keylen);

// Insert entry in hashmap given a hashmap and a key
void hashmap_put(HashMap *map, char *key, void *val);

// Insert entry in hashmap given a hashmap, a key and key length
void hashmap_put_wlen(HashMap *map, char *key, int keylen, void *val);

// Delete entry in hashmap given a hashmap and a key
void hashmap_delete(HashMap *map, char *key);

// Delete entry in hashmap given a hashmap, a key and key length
void hashmap_delete_wlen(HashMap *map, char *key, int keylen);

// Test hashmap
void hashmap_test(void);

//
// main.c
//

// Returns true if `path` to file exists
bool file_exists(char *path);

extern StringArray include_paths;
extern bool opt_fpic;
extern bool opt_fcommon;
extern char *base_file;
