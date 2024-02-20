cmake_minimum_required(VERSION 3.27)
project(acec C)

set(CMAKE_C_STANDARD 23)

add_executable(acec
        definitions/errmsg.h
        definitions/file.h
        definitions/paths.h
        definitions/syntax.h
        definitions/vinfo.h
        src/x86/acec.h
        src/x86/codegen.c
        src/x86/parse.c
        src/x86/main.c
        src/x86/parse.c
        src/x86/preproc.c
        src/x86/hashmap.c
        src/x86/str.c
        src/x86/tok.c
        src/x86/type.c
        src/x86/utf.c
)
