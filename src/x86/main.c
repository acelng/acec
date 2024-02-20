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
// Created by Luca Mazza on 2024/2/6.
// TODO: Adapt to ace

#include "acec.h"
#include "../../definitions/syntax.h"
#include "../../definitions/errmsg.h"
#include "../../definitions/vinfo.h"
#include "../../definitions/file.h"

typedef enum {
    FILE_NONE,
    FILE_ACE,
    FILE_ASM,
    FILE_O,
    FILE_AR,
    FILE_DSO
} FileType;

StringArray include_paths;

bool opt_fcommon;

bool opt_fpic;

static FileType opt_x;

static StringArray opt_include;

static bool opt_E;

static bool opt_M;

static bool opt_MD;

static bool opt_MMD;

static bool opt_MP;

static bool opt_S;

static bool opt_c;

static bool opt_cc1;

static bool opt_hash_hash_hash;

static bool opt_static;

static bool opt_shared;

static char *opt_MF;

static char *opt_MT;

static char *opt_o;

static StringArray ld_extra_args;

static StringArray std_include_paths;

char *base_file;

static char *output_file;

static StringArray input_paths;

static StringArray tmp_files;

static void usage(int status) {
    fprintf(stderr, USAGE);
    exit(status);
}

static bool take_arg(char *arg) {
    char *x[] = {
            "-o", "-I", "-idirafter", "-include", "-x", "-MF", "-MT", "-Xlinker"
    };
    for (int i = 0; i < sizeof(x) / sizeof(*x); i++)
        if (!strcmp(arg, x[i])) return true;
    return false;
}

static void add_default_include_paths(char *argv0) {
    strarray_push(&include_paths, format("%s/include", dirname(strdup(argv0))));
    strarray_push(&include_paths, "/usr/local/include");
    strarray_push(&include_paths, "/ /include/x86_64-linux-gnu");
    strarray_push(&include_paths, "/usr/include");
    for (int i = 0; i < include_paths.len; i++)
        strarray_push(&std_include_paths, include_paths.data[i]);
}

static void define(char *str) {
    char *eq = strchr(str, '=');
    if (eq) define_macro(strndup(str, eq - str), eq + 1);
    else define_macro(str, "1");
}

static FileType parse_opt_x(char *s) {
    if (!strcmp(s, "ace")) return FILE_ACE;
    if (!strcmp(s, "assembler")) return FILE_ASM;
    if (!strcmp(s, "none")) return FILE_NONE;
    error(UNKNOWN_ARG, s);
}

static char *quote_makefile(char *s) {
    char *buf = calloc(1, strlen(s) * 2 + 1);
    for (int i = 0, j = 0; s[i]; i++) {
        switch (s[i]) {
            case PT_DOLLAR:
                buf[j++] = PT_DOLLAR;
                buf[j++] = PT_DOLLAR;
                break;
            case PT_HASH:
                buf[j++] = PT_BACKSLASH;
                buf[j++] = PT_HASH;
                break;
            case ' ': case ES_TAB:
                for (int k = i - 1; k >= 0 && s[k] == PT_BACKSLASH; k--) buf[j++] = PT_BACKSLASH;
                buf[j++] = PT_BACKSLASH;
                buf[j++] = s[i];
                break;
            default:
                buf[j++] = s[i];
                break;
        }
    }
    return buf;
}

static void print_version(void) {
    char *earlier = VERSION_YEAR > 24 ? " and earlier" : "";
    printf("The ace compiler (acec); %s\n", VERSION_STRING);
    printf("\n    Compiles ace%d (%s) software%s.\n", VERSION_YEAR, VERSION_NAME, earlier);
    printf("    Find out more at %s.\n", URL_GITHUB);
    printf("\nCopyright 2024 © %s\n", AUTHOR_NAME);
}

static void parse_args(int argc, char **argv) {
    // Make sure that all command line options that take an argument
    // have an argument.
    for (int i = 1; i < argc; i++)
        if (take_arg(argv[i]))
            if (!argv[++i]) usage(1);
    StringArray idirafter = {};
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "-###")) {
            opt_hash_hash_hash = true;
            continue;
        }
        if (!strcmp(argv[i], "-cc1")) {
            opt_cc1 = true;
            continue;
        }
        if (!strcmp(argv[i], "--help")) usage(0);
        if (!strcmp(argv[i], "-o")) {
            opt_o = argv[++i];
            continue;
        }
        if (!strncmp(argv[i], "-o", 2)) {
            opt_o = argv[i] + 2;
            continue;
        }
        if (!strcmp(argv[i], "-S")) {
            opt_S = true;
            continue;
        }
        if (!strcmp(argv[i], "-fcommon")) {
            opt_fcommon = true;
            continue;
        }
        if (!strcmp(argv[i], "-fno-common")) {
            opt_fcommon = false;
            continue;
        }
        if (!strcmp(argv[i], "-c")) {
            opt_c = true;
            continue;
        }
        if (!strcmp(argv[i], "-E")) {
            opt_E = true;
            continue;
        }
        if (!strncmp(argv[i], "-I", 2)) {
            strarray_push(&include_paths, argv[i] + 2);
            continue;
        }
        if (!strcmp(argv[i], "-D")) {
            define(argv[++i]);
            continue;
        }
        if (!strncmp(argv[i], "-D", 2)) {
            define(argv[i] + 2);
            continue;
        }
        if (!strcmp(argv[i], "-U")) {
            undefine_macro(argv[++i]);
            continue;
        }
        if (!strncmp(argv[i], "-U", 2)) {
            undefine_macro(argv[i] + 2);
            continue;
        }
        if (!strcmp(argv[i], "-include")) {
            strarray_push(&opt_include, argv[++i]);
            continue;
        }
        if (!strcmp(argv[i], "-x")) {
            opt_x = parse_opt_x(argv[++i]);
            continue;
        }
        if (!strncmp(argv[i], "-x", 2)) {
            opt_x = parse_opt_x(argv[i] + 2);
            continue;
        }
        if (!strncmp(argv[i], "-l", 2) || !strncmp(argv[i], "-Wl,", 4)) {
            strarray_push(&input_paths, argv[i]);
            continue;
        }
        if (!strcmp(argv[i], "-Xlinker")) {
            strarray_push(&ld_extra_args, argv[++i]);
            continue;
        }
        if (!strcmp(argv[i], "-s")) {
            strarray_push(&ld_extra_args, "-s");
            continue;
        }
        if (!strcmp(argv[i], "-M")) {
            opt_M = true;
            continue;
        }
        if (!strcmp(argv[i], "-MF")) {
            opt_MF = argv[++i];
            continue;
        }
        if (!strcmp(argv[i], "-MP")) {
            opt_MP = true;
            continue;
        }
        if (!strcmp(argv[i], "-MT")) {
            if (opt_MT == NULL) opt_MT = argv[++i];
            else opt_MT = format("%s %s", opt_MT, argv[++i]);
            continue;
        }
        if (!strcmp(argv[i], "-MD")) {
            opt_MD = true;
            continue;
        }
        if (!strcmp(argv[i], "-MQ")) {
            if (opt_MT == NULL) opt_MT = quote_makefile(argv[++i]);
            else opt_MT = format("%s %s", opt_MT, quote_makefile(argv[++i]));
            continue;
        }
        if (!strcmp(argv[i], "-MMD")) {
            opt_MD = opt_MMD = true;
            continue;
        }
        if (!strcmp(argv[i], "-fpic") || !strcmp(argv[i], "-fPIC")) {
            opt_fpic = true;
            continue;
        }
        if (!strcmp(argv[i], "-cc1-input")) {
            base_file = argv[++i];
            continue;
        }

        if (!strcmp(argv[i], "-cc1-output")) {
            output_file = argv[++i];
            continue;
        }
        if (!strcmp(argv[i], "-idirafter")) {
            strarray_push(&idirafter, argv[i++]);
            continue;
        }
        if (!strcmp(argv[i], "-static")) {
            opt_static = true;
            strarray_push(&ld_extra_args, "-static");
            continue;
        }
        if (!strcmp(argv[i], "-shared")) {
            opt_shared = true;
            strarray_push(&ld_extra_args, "-shared");
            continue;
        }
        if (!strcmp(argv[i], "-L")) {
            strarray_push(&ld_extra_args, "-L");
            strarray_push(&ld_extra_args, argv[++i]);
            continue;
        }
        if (!strncmp(argv[i], "-L", 2)) {
            strarray_push(&ld_extra_args, "-L");
            strarray_push(&ld_extra_args, argv[i] + 2);
            continue;
        }
        if (!strcmp(argv[i], "-hashmap-test")) {
            hashmap_test();
            exit(0);
        }
        if (!strcmp(argv[i], "-v")) {
            print_version();
            exit(0);
        }
        // These options are ignored for now.
        if (!strncmp(argv[i], "-O", 2) ||
            !strncmp(argv[i], "-W", 2) ||
            !strncmp(argv[i], "-g", 2) ||
            !strncmp(argv[i], "-std=", 5) ||
            !strcmp(argv[i], "-ffreestanding") ||
            !strcmp(argv[i], "-fno-builtin") ||
            !strcmp(argv[i], "-fno-omit-frame-pointer") ||
            !strcmp(argv[i], "-fno-stack-protector") ||
            !strcmp(argv[i], "-fno-strict-aliasing") ||
            !strcmp(argv[i], "-m64") ||
            !strcmp(argv[i], "-mno-red-zone") ||
            !strcmp(argv[i], "-w"))
            continue;
        if (argv[i][0] == '-' && argv[i][1] != ES_NUL) error("unknown argument: %s", argv[i]);
        strarray_push(&input_paths, argv[i]);
    }
    for (int i = 0; i < idirafter.len; i++) strarray_push(&include_paths, idirafter.data[i]);
    if (input_paths.len == 0) error(MISSING_IN_FILE);
    // -E implies that the input is the C macro language.
    if (opt_E) opt_x = FILE_ACE;
}

static FILE *open_file(char *path) {
    if (!path || strcmp(path, OP_SUB) == 0) return stdout;
    FILE *out = fopen(path, "w");
    if (!out) error(CANNOT_OPEN_OUTPUT_FILE, path, strerror(errno));
    return out;
}

static bool endswith(char *p, char *q) {
    int len1 = strlen(p);
    int len2 = strlen(q);
    return (len1 >= len2) && !strcmp(p + len1 - len2, q);
}

// Replace file extension
static char *replace_extn(char *tmpl, char *extn) {
    char *filename = basename(strdup(tmpl));
    char *dot = strrchr(filename, '.');
    if (dot) *dot = ES_NUL;
    return format("%s%s", filename, extn);
}

static void cleanup(void) {
    for (int i = 0; i < tmp_files.len; i++) unlink(tmp_files.data[i]);
}

static char *create_tmpfile(void) {
    char *path = strdup("/tmp/acec-XXXXXX");
    int fd = mkstemp(path);
    if (fd == -1) error(MKSTEMP_FAILED, strerror(errno));
    close(fd);
    strarray_push(&tmp_files, path);
    return path;
}

static void run_subprocess(char **argv) {
    // If -### is given, dump the subprocess's command line.
    if (opt_hash_hash_hash) {
        fprintf(stderr, "%s", argv[0]);
        for (int i = 1; argv[i]; i++) fprintf(stderr, " %s", argv[i]);
        fprintf(stderr, "\n");
    }

    if (fork() == 0) {
        // Child process. Run a new command.
        execvp(argv[0], argv);
        fprintf(stderr, "exec failed: %s: %s\n", argv[0], strerror(errno));
        _exit(1);
    }

    // Wait for the child process to finish.
    int status;
    while (wait(&status) > 0);
    if (status != 0) exit(1);
}

static void run_cc1(int argc, char **argv, char *input, char *output) {
    char **args = calloc(argc + 10, sizeof(char *));
    memcpy(args, argv, argc * sizeof(char *));
    args[argc++] = "-cc1";
    if (input) {
        args[argc++] = "-cc1-input";
        args[argc++] = input;
    }
    if (output) {
        args[argc++] = "-cc1-output";
        args[argc++] = output;
    }
    run_subprocess(args);
}

// Print tokens to stdout. Used for -E.
static void print_tokens(Token *tok) {
    FILE *out = open_file(opt_o ? opt_o : OP_SUB);
    int line = 1;
    for (; tok->kind != TK_EOF; tok = tok->next) {
        if (line > 1 && tok->at_sol) fprintf(out, "\n");
        if (tok->has_space && !tok->at_sol) fprintf(out, " ");
        fprintf(out, "%.*s", tok->len, tok->loc);
        line++;
    }
    fprintf(out, "\n");
}

static bool in_std_include_path(char *path) {
    for (int i = 0; i < std_include_paths.len; i++) {
        char *dir = std_include_paths.data[i];
        int len = strlen(dir);
        if (strncmp(dir, path, len) == 0 && path[len] == '/') return true;
    }
    return false;
}

// If -M options is given, the compiler write a list of input files to
// stdout in a format that "make" command can read. This feature is
// used to automate file dependency management.
static void print_dependencies(void) {
    char *path;
    if (opt_MF) path = opt_MF;
    else if (opt_MD) path = replace_extn(opt_o ? opt_o : base_file, EXT_PRGM_DEP);
    else if (opt_o) path = opt_o;
    else path = OP_SUB;
    FILE *out = open_file(path);
    if (opt_MT) fprintf(out, "%s:", opt_MT);
    else fprintf(out, "%s:", quote_makefile(replace_extn(base_file, EXT_PRGM_OBJ)));
    File **files = get_input_files();
    for (int i = 0; files[i]; i++) {
        if (opt_MMD && in_std_include_path(files[i]->name)) continue;
        fprintf(out, " \\\n  %s", files[i]->name);
    }
    fprintf(out, "\n\n");
    if (opt_MP) {
        for (int i = 1; files[i]; i++) {
            if (opt_MMD && in_std_include_path(files[i]->name)) continue;
            fprintf(out, "%s:\n\n", quote_makefile(files[i]->name));
        }
    }
}

static Token *must_tokenize_file(char *path) {
    Token *tok = tokenize_file(path);
    if (!tok) error("%s: %s", path, strerror(errno));
    return tok;
}

static Token *append_tokens(Token *tok1, Token *tok2) {
    if (!tok1 || tok1->kind == TK_EOF) return tok2;
    Token *t = tok1;
    while (t->next->kind != TK_EOF) t = t->next;
    t->next = tok2;
    return tok1;
}

static void cc1(void) {
    Token *tok = NULL;
    // Process -include option
    for (int i = 0; i < opt_include.len; i++) {
        char *incl = opt_include.data[i];
        char *path;
        if (file_exists(incl)) {
            path = incl;
        } else {
            path = search_include_paths(incl);
            if (!path) error("-include: %s: %s", incl, strerror(errno));
        }
        Token *tok2 = must_tokenize_file(path);
        tok = append_tokens(tok, tok2);
    }
    // Tokenize and parse.
    Token *tok2 = must_tokenize_file(base_file);
    tok = append_tokens(tok, tok2);
    tok = preprocess(tok);
    // If -M or -MD are given, print file dependencies.
    if (opt_M || opt_MD) {
        print_dependencies();
        if (opt_M) return;
    }
    // If -E is given, print out preprocessed C code as a result.
    if (opt_E) {
        print_tokens(tok);
        return;
    }
    Obj *prog = parse(tok);
    // Open a temporary output buffer.
    char *buf;
    size_t buflen;
    FILE *output_buf = open_memstream(&buf, &buflen);
    // Traverse the AST to emit assembly.
    codegen(prog, output_buf);
    fclose(output_buf);
    // Write the asembly text to a file.
    FILE *out = open_file(output_file);
    fwrite(buf, buflen, 1, out);
    fclose(out);
}

static void assemble(char *input, char *output) {
    char *cmd[] = {"as", "-c", input, "-o", output, NULL};
    run_subprocess(cmd);
}

static char *find_file(char *pattern) {
    char *path = NULL;
    glob_t buf = {};
    glob(pattern, 0, NULL, &buf);
    if (buf.gl_pathc > 0) path = strdup(buf.gl_pathv[buf.gl_pathc - 1]);
    globfree(&buf);
    return path;
}

// Returns true if a given file exists.
bool file_exists(char *path) {
    struct stat st;
    return !stat(path, &st);
}

static char *find_libpath(void) {
    if (file_exists("/usr/lib/x86_64-linux-gnu/crti.o")) return "/usr/lib/x86_64-linux-gnu";
    if (file_exists("/usr/lib64/crti.o")) return "/usr/lib64";
    error(LIBPATH_NOT_FOUND);
}

static void run_linker(StringArray *inputs, char *output) {
    StringArray arr = {};
    strarray_push(&arr, "ld");
    strarray_push(&arr, "-o");
    strarray_push(&arr, output);
    strarray_push(&arr, "-m");
    strarray_push(&arr, "elf_x86_64");
    char *libpath = find_libpath();
    if (opt_shared) {
        strarray_push(&arr, format("%s/crti.o", libpath));
    } else {
        strarray_push(&arr, format("%s/crt1.o", libpath));
        strarray_push(&arr, format("%s/crti.o", libpath));
    }
    strarray_push(&arr, "-L/usr/lib/x86_64-linux-gnu");
    strarray_push(&arr, "-L/usr/lib64");
    strarray_push(&arr, "-L/lib64");
    strarray_push(&arr, "-L/usr/lib/x86_64-linux-gnu");
    strarray_push(&arr, "-L/usr/lib/x86_64-pc-linux-gnu");
    strarray_push(&arr, "-L/usr/lib/x86_64-redhat-linux");
    strarray_push(&arr, "-L/usr/lib");
    strarray_push(&arr, "-L/lib");
    if (!opt_static) {
        strarray_push(&arr, "-dynamic-linker");
        strarray_push(&arr, "/lib64/ld-linux-x86-64.so.2");
    }
    for (int i = 0; i < ld_extra_args.len; i++) strarray_push(&arr, ld_extra_args.data[i]);
    for (int i = 0; i < inputs->len; i++) strarray_push(&arr, inputs->data[i]);
    if (opt_static) {
        strarray_push(&arr, "--start-group");
        strarray_push(&arr, "-lgcc");
        strarray_push(&arr, "-lgcc_eh");
        strarray_push(&arr, "-lc");
        strarray_push(&arr, "--end-group");
    } else {
        strarray_push(&arr, "-lc");
        strarray_push(&arr, "-lgcc");
        strarray_push(&arr, "--as-needed");
        strarray_push(&arr, "-lgcc_s");
        strarray_push(&arr, "--no-as-needed");
    }
    strarray_push(&arr, format("%s/crtn.o", libpath));
    strarray_push(&arr, NULL);
    run_subprocess(arr.data);
}

static FileType get_file_type(char *filename) {
    if (opt_x != FILE_NONE) return opt_x;
    if (endswith(filename, ".a")) return FILE_AR;
    if (endswith(filename, ".so")) return FILE_DSO;
    if (endswith(filename, EXT_PRGM_OBJ)) return FILE_O;
    if (endswith(filename, EXT_PRGM)) return FILE_ACE;
    if (endswith(filename, ".s")) return FILE_ASM;
    error("<command line>: unknown file extension: %s", filename);
}

int main(int argc, char **argv) {
    atexit(cleanup);
    init_macros();
    parse_args(argc, argv);
    if (opt_cc1) {
        add_default_include_paths(argv[0]);
        cc1();
        return 0;
    }
    if (input_paths.len > 1 && opt_o && (opt_c || opt_S | opt_E))
        error("cannot specify '-o' with '-c,' '-S' or '-E' with multiple files");
    StringArray ld_args = {};
    for (int i = 0; i < input_paths.len; i++) {
        char *input = input_paths.data[i];
        if (!strncmp(input, "-l", 2)) {
            strarray_push(&ld_args, input);
            continue;
        }
        if (!strncmp(input, "-Wl,", 4)) {
            char *s = strdup(input + 4);
            char *arg = strtok(s, ",");
            while (arg) {
                strarray_push(&ld_args, arg);
                arg = strtok(NULL, ",");
            }
            continue;
        }
        char *output;
        if (opt_o) output = opt_o;
        else if (opt_S) output = replace_extn(input, ".s");
        else output = replace_extn(input, ".o");
        FileType type = get_file_type(input);
        // Handle .o or .a
        if (type == FILE_O || type == FILE_AR || type == FILE_DSO) {
            strarray_push(&ld_args, input);
            continue;
        }
        // Handle .s
        if (type == FILE_ASM) {
            if (!opt_S)
                assemble(input, output);
            continue;
        }
        assert(type == FILE_ACE);
        // Just preprocess
        if (opt_E || opt_M) {
            run_cc1(argc, argv, input, NULL);
            continue;
        }
        // Compile
        if (opt_S) {
            run_cc1(argc, argv, input, output);
            continue;
        }
        // Compile and assemble
        if (opt_c) {
            char *tmp = create_tmpfile();
            run_cc1(argc, argv, input, tmp);
            assemble(tmp, output);
            continue;
        }
        // Compile, assemble and link
        char *tmp1 = create_tmpfile();
        char *tmp2 = create_tmpfile();
        run_cc1(argc, argv, input, tmp1);
        assemble(tmp1, tmp2);
        strarray_push(&ld_args, tmp2);
    }
    if (ld_args.len > 0) run_linker(&ld_args, opt_o ? opt_o : "a.out");
    return 0;
}