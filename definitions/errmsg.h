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
// Created by Luca Mazza on 2024/2/10.
//

// TYPES
#define CANNOT_INFER_TYPE       "cannot infer type"
#define INCOMPLETE_TYPE         "variable has incomplete type"

// POINTERS
#define CANNOT_DEFERENCE_PTR    "invalid pointer dereference"
#define CANNOT_DEFERENCE_VOID   "dereferencing a void pointer"
#define CANNOT_RET_VOID_STMT    "statement expression returning void is not supported"

// UNEXPECTED TOKENS
#define UNEXPECTED_TOKEN        "unexpected token"
#define UNEXPECTED_DPOUND_SOE   "'##' cannot appear at start of macro expansion"
#define UNEXPECTED_DPOUND_EOE   "'##' cannot appear at end of macro expansion"
#define UNEXPECTED_ST_CL        "unexpected storage class specifier"
#define UNEXPECTED              "unexpected %s"

// EXPECTED TOKENS BUT MISSING
#define EXPECTED_STR           "expected %s"
#define EXPECTED_LVALUE        "lvalue expected"
#define EXPECTED_ID            "identifier expected"
#define EXPECTED_ID_MACRO_NAME  "macro name must be an identifier"
#define EXPECTED_CONST_EXPR     "constant expression expected"
#define EXPECTED_PTR            "pointer type expected"
#define MISSING_MACRO_PARAM     "'#' is not followed by a macro parameter"
#define MISSING_FILENAME        "file name expected"
#define MISSING_VARNAME         "variable name omitted"
#define EXPECTED_STR_LITERAL    "expected string literal"
// UNTERMINATED TOKENS
#define UNT_MACRO_ARG           "unterminated macro argument"
#define UNT_INCLUDE             "unterminated include"
#define UNT_COND_DIR            "unterminated conditional directive"
#define UNT_BCOMMENT            "unterminated block comment"
#define UNT_STR                 "unterminated string literal"
#define UNT_CHAR                "unterminated char literal"

// OVERFLOW
#define TOO_MANY_ARGS           "too many macro arguments"

// UNKNOWN
#define UNK_ENUM_TY             "unknown enum type"

// INVALID TOKENS
#define INV_EXPR                "invalid expression"
#define INV_TOK                 "invalid token"
#define INV_STMT                "invalid statement"
#define INV_TOKEN_PASTE         "pasting forms '%s', that is an invalid token"
#define INV_PP_DIR              "invalid preprocessor directive"
#define INV_LINE_MARK           "invalid line marker"
#define INV_NUM_CONST           "invalid numeric constant"
#define INV_HEX_ESC_SEQ         "invalid hex escape sequence"
#define INV_TYPEDEF             "typedef cannot be static, extern, inline, or tls"
#define INV_TYPE                "invalid type"
#define INV_ENUM_TYPE           "invalid enum type"
#define INVALID_OP              "invalid operands"

// FILE
#define CANNOT_OPEN_FILE        "%s: cannot open file: %s"
#define CANNOT_OPEN_OUTPUT_FILE "cannot open output file: %s: %s"
#define MKSTEMP_FAILED          "file name templating failed: %s"
#define LIBPATH_NOT_FOUND       "library path not found"
#define MISSING_IN_FILE         "missing file to compile"

// STRAY TOKEN
#define STRAY_PP_TOKEN          "stray #%s"

// NON-STANDARD OPERATIONS
#define NSTD_CONCAT             "unsupported non-standard concatenation of string literals"

// COMMAND ERRORS
#define UNKNOWN_ARG             "<command line>: unknown argument for -x: %s"

// UNDEFINED ERRORS
#define NO_SUCH_KEY             "no such key"

// USAGE
#define USAGE                   "Usage: acec [options] <file>\n"

// DECLARATION
#define VOID_DECLARATION        "variable declared as void"
#define CANNOT_INIT_VLA         "variable length objects cannot be initialized"
#define DESIGNATOR_OOB          "array designator index exceeds array bounds"
#define DESIGNATOR_RANGE_EMPTY  "array designator range [%d, %d] is empty"
#define CASE_RANGE_EMPTY        "case range [%d, %d] is empty"
#define EXPECTED_MEM_NAME       "expected member name"
#define NO_SUCH_MEMBER          "no such member in struct"
#define NOT_ARRAY_INIT          "array index int non-array initializer"
#define FIEND_NAME              "fiend name not in struct or union initializer"
#define INVALID_INIT            "invalid initializer"
#define NOT_CT_CONST            "not a compile-time constant"
#define CANNOT_ADDR_BITF        "cannot address bitfield"
#define UNKNOWN_ATTR            "unknown attribute"
#define NO_STRUCT_UNION         "not a struct nor a union"
#define NO_SUCH_MEMBER2         "no such member"
#define NOT_FUNC                "not a function"
#define TOO_MANY_ARGUMENTS      "too many args"
#define TOO_FEW_ARGUMENTS       "too few args"
#define CTRL_EXPR_TYPE_NC       "controlling expression type not compatible with any generic association type"
#define IMPLICIT_DECL           "implicit declaration of a function"
#define UNDEF_VAR               "undefined variable"
#define EXPECTED_EXPR           "expected expression"
#define ALIAS_NAME_OMITTED      "alias name omitted"
#define PARAM_NAME_OMITTED      "param name omitted"
#define FUNC_NAME_OMITTED       "function name omitted"
#define USE_UNDECL_LABEL        "use of an undeclared label"
#define REDECL_FUNC             "redeclared as a different kind of symbol"
#define REDEF_FUNC              "redefinition of %s"
#define STATIC_NONSTATIC        "static declaration follows a non-static declaration"

// UTF
#define INVALID_UTF8            "invalid UTF-8 sequence"