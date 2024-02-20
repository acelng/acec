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
// Created by Luca Mazza on 2024/2/8.
//

// Types
#define KW_BOOL             "bool"
#define KW_CHAR             "char"
#define KW_SHORT            "int16"
#define KW_INT              "int32"
#define KW_LONG             "int64"
#define KW_FLOAT            "float32"
#define KW_DOUBLE           "float64"
#define KW_UCHAR            "uchar"
#define KW_USHORT           "uint16"
#define KW_UINT             "uint32"
#define KW_ULONG            "uint64"
#define KW_LDOUBLE          "float80"
#define KW_CONST            "fix"
#define KW_SIGNED           "s"
#define KW_UNSIGNED         "u"
#define KW_VOID             "void"

// Variables & Functions
#define KW_EXTERN           "outs"
#define KW_RESTRICT         "limit"
#define KW_INLINE           "inline"
#define KW_STATIC           "static"
#define KW_REGISTER         "keep"
#define KW_RETURN           "yield"
#define KW_VOLATILE         "vlt"

// Selection
#define KW_IF               "if"
#define KW_ELSE             "else"
#define KW_SWITCH           "switch"
#define KW_CASE             "case"
#define KW_DEFAULT          "default"
#define KW_BREAK            "stop"
#define KW_CONTINUE         "next"

// Iteration
#define KW_DO               "do"
#define KW_WHILE            "while"
#define KW_FOR              "for"
#define KW_GOTO             "jump"

// Structures
#define KW_STRUCT           "struct"
#define KW_UNION            "union"
#define KW_ENUM             "enum"
#define KW_TYPEDEF          "alias"

// Others
#define KW_SIZEOF           "szof"
#define KW_TYPEOF           "type"

// Macros
#define PP_INCLUDE          "incl"
#define PP_INCLUDE_NEXT     "incn"
#define PP_DEFINE           "define"
#define PP_UNDEF            "undef"

// Preprocessor selection
#define PP_DEFINED          "def"
#define PP_IFDEF            "ifdef"
#define PP_IFNDEF           "ifndef"
#define PP_ELIF             "elif"
#define PP_ENDIF            "endif"

#define PP_THREAD           "thread"
#define PP_THREAD_LOCAL     "threadl"
#define PP_NORETURN         "noyield"
#define PP_ATTRIBUTE        "attr"
#define PP_ATOMIC           "atomic"
#define PP_ALIGNAS          "alignas"
#define PP_LINE             "line"
#define PP_PRAGMA           "pragma"
#define PP_ERROR            "error"
#define PP_VARARGS          "vargs"
#define PP_ALIGNOF          "alignof"
#define PP_ASM              "asm"
#define PP_PACKED           "pack"
#define PP_ALINGED          "aligned"
#define PP_GENERIC          "generic"
#define PP_VAREA            "varea"
#define PP_ALLOC_SIZE       "allocsz"
#define PP_FUNCTION         "func"
#define PP_ALLOCA           "alloca"

// Preprocessor symbols
#define PP_POUND            "#"
#define PP_POUND_POUND      "##"

// Assignment operators
#define OP_ASSIGN           "="
#define OP_ASSIGN_ADD       "+="
#define OP_ASSIGN_SUB       "-="
#define OP_ASSIGN_MUL       "*="
#define OP_ASSIGN_DIV       "/="
#define OP_ASSIGN_MOD       "%="
#define OP_ASSIGN_SHL       "<<="
#define OP_ASSIGN_SHR       ">>="
#define OP_ASSIGN_AND       "&="
#define OP_ASSIGN_OR        "|="
#define OP_ASSIGN_XOR       "^="

// Binary operators
#define OP_ADD              "+"
#define OP_SUB              "-"
#define OP_MUL              "*"
#define OP_DIV              "/"
#define OP_MOD              "%"
#define OP_SHL              "<<"
#define OP_SHR              ">>"
#define OP_AND              "&"
#define OP_OR               "|"
#define OP_XOR              "^"
#define OP_NOT              "~"

// Logical operators
#define OP_LOG_AND          "&&"
#define OP_LOG_OR           "||"
#define OP_LOG_NOT          "!"
#define OP_LOG_EQ           "=="
#define OP_LOG_NE           "!="
#define OP_LOG_LT           "<"
#define OP_LOG_LE           "<="
#define OP_LOG_GT           ">"
#define OP_LOG_GE           ">="

// Unary operators
#define OP_INCR             "++"
#define OP_DECR             "--"

// Shift operators
#define OP_SHL              "<<"
#define OP_SHR              ">>"

// Punctuation
#define PT_VARARGS          "..."
#define PT_QUEST            "?"
#define PT_COLON            ":"
#define PT_PAREN_OPEN       "("
#define PT_PAREN_CLOSE      ")"
#define PT_BRACE_OPEN       "{"
#define PT_BRACE_CLOSE      "}"
#define PT_BRACKET_OPEN     "["
#define PT_BRACKET_CLOSE    "]"
#define PT_SEMICOLON        ";"
#define PT_ARROW            "->"
#define PT_COMMA            ","
#define PT_POINT            "."
#define PT_QUOTE            '"'
#define PT_BACKSLASH        '\\'
#define PT_DOLLAR           '$'
#define PT_HASH             '#'

// Escape characters
#define ES_NL               '\n'
#define ES_ALERT            '\a'
#define ES_BACKSPACE        '\b'
#define ES_TAB              '\t'
#define ES_VTAB             '\v'
#define ES_FORM_FEED        '\f'
#define ES_CR               '\r'
#define ES_NUL              '\0'

// Comments
#define INLINE_COMMENT       "//"
#define BLOCK_COMMENT_START  "/*"
#define BLOCK_COMMENT_END    "*/"
