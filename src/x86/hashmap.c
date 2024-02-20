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
// Created by Luca Mazza on 2024/2/2.
//

#include "acec.h"
#include "../../definitions/errmsg.h"

/// Initial hash bucket size
#define INIT_SIZE 16

/// Rehash if >70% usage
#define HIGH_WATERMARK 70

/// Keep usage <50% after rehash
#define LOW_WATERMARK 50

/// Deleted hash entry
#define TOMBSTONE ((void *)-1)

/// Calculates FNV-1a hash of string, given a string and length
/// https://en.wikipedia.org/wiki/Fowler%E2%80%93Noll%E2%80%93Vo_hash_function
static uint64_t fnv_hash(char *s, int len) {
    // FNV offset basis
    uint64_t hash = 0xcbf29ce484222325;
    for (int i = 0; i < len; i++) {
        // FNV prime
        hash *= 0x100000001b3;
        hash ^= (unsigned char)s[i];
    }
    return hash;
}

/// Make space for new entries in hashmap, removing
/// tombstones and extending bucket size, given a hashmap
static void rehash(HashMap *map) {
    int nkeys = 0;
    for (int i = 0; i < map->capacity; i++)
        if (map->buckets[i].key && map->buckets[i].key != TOMBSTONE) nkeys++;
    int cap = map->capacity;
    while ((nkeys * 100) / cap >= LOW_WATERMARK) cap *= 2;
    assert(cap > 0);
    HashMap map2 = {};
    map2.buckets = calloc(cap, sizeof(HashEntry));
    map2.capacity = cap;
    for (int i = 0; i < map->capacity; i++) {
        HashEntry *ent = &map->buckets[i];
        if (ent->key && ent->key != TOMBSTONE) hashmap_put_wlen(&map2, ent->key, ent->keylen, ent->val);
    }
    assert(map2.used == nkeys);
    *map = map2;
}

/// Check if entry matches key, given an entry, a key and key length
static bool match(HashEntry *ent, char *key, int keylen) {
    return ent->key && ent->key != TOMBSTONE && ent->keylen == keylen && memcmp(ent->key, key, keylen) == 0;
}

/// Get entry in hashmap, given a hashmap, a key and key length
static HashEntry *get_entry(HashMap *map, char *key, int keylen) {
    if (!map->buckets) return NULL;
    uint64_t hash = fnv_hash(key, keylen);
    for (int i = 0; i < map->capacity; i++) {
        HashEntry *ent = &map->buckets[(hash + i) % map->capacity];
        if (match(ent, key, keylen)) return ent;
        if (ent->key == NULL) return NULL;
    }
    unreachable()
}

/// Get or insert entry in hashmap given a hashmap, a key and key length
static HashEntry *get_insert_entry(HashMap *map, char *key, int keylen) {
    if (!map->buckets) {
        map->buckets = calloc(INIT_SIZE, sizeof(HashEntry));
        map->capacity = INIT_SIZE;
    } else if ((map->used * 100) / map->capacity >= HIGH_WATERMARK) rehash(map);
    uint64_t hash = fnv_hash(key, keylen);
    for (int i = 0; i < map->capacity; i++) {
        HashEntry *ent = &map->buckets[(hash + i) % map->capacity];
        if (match(ent, key, keylen)) return ent;
        if (ent->key == TOMBSTONE) {
            ent->key = key;
            ent->keylen = keylen;
            return ent;
        }
        if (ent->key == NULL) {
            ent->key = key;
            ent->keylen = keylen;
            map->used++;
            return ent;
        }
    }
    unreachable()
}

/// Get entry in hashmap given a hashmap and a key
void *hashmap_get(HashMap *map, char *key) {
    return hashmap_get_wlen(map, key, strlen(key));
}

/// Get entry in hashmap given a hashmap, a key and key length
void *hashmap_get_wlen(HashMap *map, char *key, int keylen) {
    HashEntry *ent = get_entry(map, key, keylen);
    return ent ? ent->val : NULL;
}

/// Insert entry in hashmap given a hashmap and a key
void hashmap_put(HashMap *map, char *key, void *val) {
    hashmap_put_wlen(map, key, strlen(key), val);
}

/// Insert entry in hashmap given a hashmap, a key and key length
void hashmap_put_wlen(HashMap *map, char *key, int keylen, void *val) {
    HashEntry *ent = get_insert_entry(map, key, keylen);
    ent->val = val;
}

/// Delete entry in hashmap given a hashmap and a key
void hashmap_delete(HashMap *map, char *key) {
    hashmap_delete_wlen(map, key, strlen(key));
}

/// Delete entry in hashmap given a hashmap, a key and key length
void hashmap_delete_wlen(HashMap *map, char *key, int keylen) {
    HashEntry *ent = get_entry(map, key, keylen);
    if (ent) ent->key = TOMBSTONE;
}

/// Test hashmap
void hashmap_test(void) {
    HashMap *map = calloc(1, sizeof(HashMap));
    for (int i = 0; i < 5000; i++) hashmap_put(map, format("key %d", i), (void *)(size_t)i);
    for (int i = 1000; i < 2000; i++) hashmap_delete(map, format("key %d", i));
    for (int i = 1500; i < 1600; i++) hashmap_put(map, format("key %d", i), (void *)(size_t)i);
    for (int i = 6000; i < 7000; i++) hashmap_put(map, format("key %d", i), (void *)(size_t)i);
    for (int i = 0; i < 1000; i++) assert((size_t)hashmap_get(map, format("key %d", i)) == i);
    for (int i = 1000; i < 1500; i++) assert(hashmap_get(map, "no such key") == NULL);
    for (int i = 1500; i < 1600; i++) assert((size_t)hashmap_get(map, format("key %d", i)) == i);
    for (int i = 1600; i < 2000; i++) assert(hashmap_get(map, "no such key") == NULL);
    for (int i = 2000; i < 5000; i++) assert((size_t)hashmap_get(map, format("key %d", i)) == i);
    for (int i = 5000; i < 6000; i++) assert(hashmap_get(map, "no such key") == NULL);
    for (int i = 6000; i < 7000; i++) hashmap_put(map, format("key %d", i), (void *)(size_t)i);
    assert(hashmap_get(map, NO_SUCH_KEY) == NULL);
    printf("OK\n");
}