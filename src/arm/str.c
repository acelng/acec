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

/// Pushes a new string into the `StringArray`
void strarray_push(StringArray *arr, char *s) {
    if (!arr->data) {
        arr->data = calloc(8, sizeof(char *));
        arr->capacity=8;
    }
    if (arr->capacity == arr->len) {
        arr->data = realloc(arr->data, sizeof(char *) * arr->capacity * 2);
        arr->capacity *= 2;
        for (int i = arr->len; i < arr->capacity; i++) arr->data[i] = NULL; // (int )
    }
    arr->data[arr->len++] = s;
}

/// Returns a formatted string given a format and arguments
char *format(char *fmt, ...) {
    char *buf;
    size_t buflen;
    FILE *out = open_memstream(&buf, &buflen);
    va_list ap;
    va_start(ap, fmt);
    vfprintf(out, fmt, ap);
    va_end(ap);
    fclose(out);
    return buf;
}