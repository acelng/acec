cmake_minimum_required(VERSION 3.27)
project(acec C)

set(CMAKE_C_STANDARD 23)

add_executable(acec
        definitions/errmsg.h
        definitions/file.h
        definitions/paths.h
        definitions/syntax.h
        definitions/vinfo.h
        src/arm/acec.h
        src/arm/codegen.c
        src/arm/parse.c
        src/arm/main.c
        src/arm/parse.c
        src/arm/preproc.c
        src/arm/hashmap.c
        src/arm/str.c
        src/arm/tok.c
        src/arm/type.c
        src/arm/utf.c
)
