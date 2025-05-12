#define _POSIX_C_SOURCE 199309L  // for clock_gettime, CLOCK_MONOTONIC

#include <unistd.h>
#include <time.h>
#include <stdint.h>

#include "dr_api.h"
#include "drmgr.h"
#include "drutil.h"
#include "drreg.h"
#include "drwrap.h"
#include "drsyms.h"
#include <stddef.h>
#include <string.h>
#include <stdio.h>
#include "utils.h"
#include "uthash.h" // Include uthash header

//#define INITIAL_REGION_CAPACITY 20
#define INITIAL_REGION_CAPACITY 8192
//#define INITIAL_REGION_CAPACITY 16384
//#define INITIAL_REGION_CAPACITY 32768
//#define INITIAL_REGION_CAPACITY 65536
//#define INITIAL_REGION_CAPACITY 1048576
#define MAX_SAFE_CAPACITY 10000000
#define MALLOC_ROUTINE_NAME "malloc"
#define CALLOC_ROUTINE_NAME "calloc"
#define REALLOC_ROUTINE_NAME "realloc"
#define FREE_ROUTINE_NAME "free"
#define DR_LOG_MASK_BASEOFFSET 0x80000000
#define FUNC_CALL_TRIGGER_THRESHOLD 1000

#ifndef OUT
#define OUT
#endif

typedef struct _memory_region_t {
    void *base_address;
    size_t size;
    bool is_active;
    int next_free;  // For free list linkage
    int pid;
} memory_region_t;

typedef struct {
    file_t log;
    FILE *logf;
    size_t size;
    bool from_calloc;
    bool from_realloc;
} per_thread_t;

typedef struct {
    reg_id_t reg_id;
    size_t offset;
} reg_map_t;

// uthash structure
typedef struct {
    int pid;
    void *ptr;
} HashKey;

typedef struct {
    HashKey key;         // malloc address
    unsigned int value;  // region index
    size_t size;         // region size
    UT_hash_handle hh; // uthash handle
} HashEntry;


const reg_map_t reg_map[] = {
    { DR_REG_RAX, offsetof(dr_mcontext_t, rax) },
    { DR_REG_RBX, offsetof(dr_mcontext_t, rbx) },
    { DR_REG_RCX, offsetof(dr_mcontext_t, rcx) },
    { DR_REG_RDX, offsetof(dr_mcontext_t, rdx) },
    { DR_REG_RSI, offsetof(dr_mcontext_t, rsi) },
    { DR_REG_RDI, offsetof(dr_mcontext_t, rdi) },
    { DR_REG_RBP, offsetof(dr_mcontext_t, rbp) },
    { DR_REG_RSP, offsetof(dr_mcontext_t, rsp) },
    { DR_REG_R8,  offsetof(dr_mcontext_t, r8) },
    { DR_REG_R9,  offsetof(dr_mcontext_t, r9) },
    { DR_REG_R10, offsetof(dr_mcontext_t, r10) },
    { DR_REG_R11, offsetof(dr_mcontext_t, r11) },
    { DR_REG_R12, offsetof(dr_mcontext_t, r12) },
    { DR_REG_R13, offsetof(dr_mcontext_t, r13) },
    { DR_REG_R14, offsetof(dr_mcontext_t, r14) },
    { DR_REG_R15, offsetof(dr_mcontext_t, r15) },
};


//static memory_region_t regions[MAX_REGIONS];
static HashEntry *hash_table = NULL;
static memory_region_t *regions = NULL;
static int region_capacity = 0;
static int free_list_head = -1;
static __thread int last_hit_index = -1;  // cached region index
static int region_count = 0;
static int test_pass = 1;
static uint64 pass_cnt = 0;
static uint64 fail_cnt = 0;
static bool debug_src_print = false;
static int stack_search_depth = 5;

static client_id_t client_id;
static void *mutex; /* for multithread support */
static int tls_idx;

static void wrap_malloc_pre(void *wrapcxt, OUT void **user_data);
static void wrap_malloc_post(void *wrapcxt, void *user_data);
static void wrap_free_pre(void *wrapcxt, OUT void **user_data);
static int lookup_region_index(void *ptr, bool *fast_hit);
void hash_table_delete(void *key, size_t size);

static void event_thread_init(void *drcontext);
static void event_thread_exit(void *drcontext);
static void event_exit(void);
static void module_load_event(void *drcontext, const module_data_t *mod, bool loaded);
static void print_disassembled_instr(void *drcontext, instr_t *instr, int verbose);
static void print_disassembled_pc(void *drcontext, app_pc instr_addr, int verbose);

static bool should_ignore_memory_access(reg_id_t base_reg);

static app_pc malloc_func  = NULL;
static app_pc calloc_func  = NULL;
static app_pc realloc_func = NULL;
static app_pc free_func    = NULL;

// Periodically report timing from other parts of the code as needed
// For example, call report_function_timing() inside memory instrumentation or every N iterations

static uint64 timer_is_in_active_region = 0, count_is_in_active_region = 0;
static uint64 timer_find_free_index = 0, count_find_free_index = 0;
static uint64 timer_wrap_malloc_post = 0, count_wrap_malloc_post = 0;
static uint64 timer_wrap_malloc_pre = 0, count_wrap_malloc_pre = 0;
static uint64 timer_wrap_free_pre = 0, count_wrap_free_pre = 0;

static void report_function_timing() {
    //dr_fprintf(STDOUT, "\n=== FUNCTION TIMING REPORT (intermediate) ===\n");
    //dr_fprintf(STDOUT, "is_in_active_region: count = %llu, total ns = %llu, avg ns = %llu\n",
    //           count_is_in_active_region, timer_is_in_active_region,
    //           count_is_in_active_region ? timer_is_in_active_region / count_is_in_active_region : 0);
    //dr_fprintf(STDOUT, "find_free_index: count = %llu, total ns = %llu, avg ns = %llu\n",
    //           count_find_free_index, timer_find_free_index,
    //           count_find_free_index ? timer_find_free_index / count_find_free_index : 0);
    //dr_fprintf(STDOUT, "wrap_malloc_post: count = %llu, total ns = %llu, avg ns = %llu\n",
    //           count_wrap_malloc_post, timer_wrap_malloc_post,
    //           count_wrap_malloc_post ? timer_wrap_malloc_post / count_wrap_malloc_post : 0);
    //dr_fprintf(STDOUT, "wrap_malloc_pre: count = %llu, total ns = %llu, avg ns = %llu\n",
    //           count_wrap_malloc_pre, timer_wrap_malloc_pre,
    //           count_wrap_malloc_pre ? timer_wrap_malloc_pre / count_wrap_malloc_pre : 0);
    //dr_fprintf(STDOUT, "wrap_free_pre: count = %llu, total ns = %llu, avg ns = %llu\n",
    //           count_wrap_free_pre, timer_wrap_free_pre,
    //           count_wrap_free_pre ? timer_wrap_free_pre / count_wrap_free_pre : 0);
}

static inline struct timespec start_profile_section(uint64 *counter) {
    (*counter)++;
    struct timespec start;
    clock_gettime(CLOCK_MONOTONIC, &start);
    return start;
}

static inline void end_profile_section(struct timespec start, uint64 *accumulator, uint64 counter, uint64 interval) {
    struct timespec end;
    clock_gettime(CLOCK_MONOTONIC, &end);
    *accumulator += (uint64)((end.tv_sec - start.tv_sec) * 1000000000LL + (end.tv_nsec - start.tv_nsec));
    if (counter % interval == 0) {
        report_function_timing();
    }
}


//void verbose_fprintf(file_t f, int level, const char *fmt, ...) {
//    if (dr_log(NULL, DR_LOG_MASK_BASEOFFSET, level, "")) {
//        va_list args;
//        va_start(args, fmt);
//        dr_vfprintf(f, fmt, args);
//        va_end(args);
//    }
//}

/* Helper function to check if the caller is from user code */
static bool is_user_malloc(void *drcontext, void *wrapcxt) {
    void *return_addr = drwrap_get_retaddr(wrapcxt);
    module_data_t *mod = dr_lookup_module(return_addr);
    if (mod != NULL) {
        //bool is_user = (strstr(mod->full_path, "/home/arkade/tools/Binary_Instrumentation_Tools/DynamoRIO/src/github/dynamorio/debug/arkade_examples/hello2") != NULL);
        bool is_user = (strstr(mod->full_path, "/home/arkade/github/evaluation/benchmarks/SPEC/cpu2017/benchspec/CPU/600.perlbench_s/run/run_base_refspeed_base_offset-m64.0000/perlbench_s_base.base_offset-m64") != NULL);
        dr_free_module_data(mod);
        return is_user;
    }
    return false;
}

static void wrap_malloc_pre(void *wrapcxt, OUT void **user_data) {
    struct timespec t = start_profile_section(&count_wrap_malloc_pre);

    //size_t size = (size_t)drwrap_get_arg(wrapcxt, 0);

    dr_mutex_lock(mutex);

    void *drcontext = drwrap_get_drcontext(wrapcxt);
    per_thread_t *data = (per_thread_t *)drmgr_get_tls_field(drcontext, tls_idx);
    //data->size = size; // Pass 'size' to wrap_malloc_post

    app_pc target = drwrap_get_func(wrapcxt);

    dr_fprintf(STDOUT, "[wrap_Alloc_pre] target=%p, malloc=%p, calloc=%p, realloc=%p, free=%p\n",
               target, malloc_func, calloc_func, realloc_func, free_func);


    if (target == malloc_func) {
        data->size = (size_t)drwrap_get_arg(wrapcxt, 0);

        if(data->from_calloc) {
            dr_fprintf(STDOUT, "[wrap_Malloc_pre] malloc is from inside calloc\n");
        } else if (data->from_realloc) {
            dr_fprintf(STDOUT, "[wrap_Malloc_pre] malloc is from inside realloc\n");
        } else {
            dr_fprintf(STDOUT, "[wrap_Malloc_pre] malloc is from malloc itself, pid=%d, size=%zu\n", getpid(), data->size);
        }
    }
    else if (target == calloc_func) {
        data->size = (size_t)drwrap_get_arg(wrapcxt, 0) * (size_t)drwrap_get_arg(wrapcxt, 1);
        data->from_calloc  = true;
        data->from_realloc = false;
        dr_fprintf(STDOUT, "[wrap_Calloc_pre] pid=%d, size=%zu\n", getpid(), data->size);
    }
    else if (target == realloc_func) {
        void *old_ptr = (void *)drwrap_get_arg(wrapcxt, 0);
        data->from_realloc = true;
        data->from_calloc  = false;
        data->size = (size_t)drwrap_get_arg(wrapcxt, 1);

        if (old_ptr != NULL) {

            bool fast_hit = false;
            int old_index = lookup_region_index(old_ptr, &fast_hit);

            if (old_index >= 0) {
                regions[old_index].is_active = false;
                regions[old_index].next_free = free_list_head;
                free_list_head = old_index;

                hash_table_delete(old_ptr, regions[old_index].size);

                dr_fprintf(STDOUT, "[wrap_Realloc_pre] pid=%d, old_ptr=%p, old_size=%zu, new_size=%zu, index=%d\n",
                                                      getpid(), old_ptr, regions[old_index].size, data->size, old_index);
            }
        } else {
            dr_fprintf(STDOUT, "[wrap_Realloc_pre] old_ptr is NULL. realloc(NULL, size) might be used somewhere for unified code management.\n");
        }
    }

    //bool is_user = is_user_malloc(dr_get_current_drcontext(), wrapcxt);

    //if (is_user) {
       //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 2, "[ARKADE MALLOC CALLED] Malloc (User Code) (size: %zu)\n", size);
    //} else {
       //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 2, "[ARKADE MALLOC CALLED] Malloc (Nonuser Code) (size: %zu)\n", size);
    //}

//    void *return_addr = drwrap_get_retaddr(wrapcxt);
//    //drsym_info_t sym;
//    //memset(&sym, 0, sizeof(sym));
//    //sym.struct_size = sizeof(sym);
//    //sym.name = (char *)dr_global_alloc(256);
//    //sym.name_size = 256;
//    //sym.file = (char *)dr_global_alloc(256);
//    //sym.file_size = 256;
//
//    static module_data_t *last_mod_malloc = NULL;
//    module_data_t *mod = NULL;
//
//    if (last_mod_malloc != NULL &&
//        (app_pc)return_addr >= last_mod_malloc->start &&
//        (app_pc)return_addr < last_mod_malloc->end) {
//        mod = last_mod_malloc;
//    } else {
//        mod = dr_lookup_module(return_addr);
//        last_mod_malloc = mod;
//    }
//
//
//    if (mod != NULL) {
//       //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "[ARKADE MALLOC CALLED] Module start: %p\n", mod->start);
//       //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "[ARKADE MALLOC CALLED] Module end: %p\n", mod->end);
//       //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "[ARKADE MALLOC CALLED] Module full path: %s\n", mod->full_path);
//
//        size_t offset = (size_t)((app_pc)return_addr - mod->start);
//
//        //dr_log(NULL, DR_LOG_MASK_BASEOFFSET, "[ARKADE] Offset: %zu\n", offset);
//
//        /* ARKADE
//        drsym_error_t sym_res = drsym_lookup_address(mod->full_path, offset, &sym, DRSYM_DEFAULT_FLAGS);
//        dr_free_module_data(mod);
//        if (sym_res == DRSYM_SUCCESS) {
//        //if (sym_res == DRSYM_SUCCESS | sym_res == DRSYM_ERROR_LINE_NOT_AVAILABLE) {
//            if (is_user) {
//               //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "[ARKADE MALLOC CALLED] Caller (User Code): %s (%s:%d)\n", sym.name, sym.file, sym.line);
//            } else {
//               //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "[ARKADE MALLOC CALLED] Caller (Nonuser Code): %s (%s:%d)\n", sym.name, sym.file, sym.line);
//            }
//        } else {
//           //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 2, "[ARKADE MALLOC CALLED] Caller: Unknown, sym_res: %d\n", sym_res);
//        }
//        */
//    } else {
//       //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 2, "[ARKADE MALLOC CALLED] Caller: Unknown, mode: NULL\n");
//    }
//
//    //dr_global_free(sym.name, 256);
//    //dr_global_free(sym.file, 256);

    dr_mutex_unlock(mutex);

    end_profile_section(t, &timer_wrap_malloc_pre, count_wrap_malloc_pre, FUNC_CALL_TRIGGER_THRESHOLD);
}

void init_region_table() {
    region_capacity = INITIAL_REGION_CAPACITY;
    regions = (memory_region_t *)dr_global_alloc(sizeof(memory_region_t) * region_capacity);
    memset(regions, 0, sizeof(memory_region_t) * region_capacity);

    for (int i = 0; i < region_capacity - 1; i++) {
        regions[i].next_free = i + 1;
    }
    regions[region_capacity - 1].next_free = -1;
    free_list_head = 0;
}

void expand_region_table() {

    if (region_capacity >= MAX_SAFE_CAPACITY) {
        dr_fprintf(STDERR,
            "[ARKADE] ERROR: Region capacity exceeded safe limit (%d regions). Aborting allocation.\n",
            region_capacity);
        return;
    }

    int old_capacity = region_capacity;
    //int new_capacity = region_capacity + 50000;
    //int new_capacity = region_capacity + 65536;
    int new_capacity = region_capacity * 2;

    memory_region_t *new_regions = (memory_region_t *)dr_global_alloc(sizeof(memory_region_t) * new_capacity);

    if (!new_regions) {
        dr_fprintf(STDERR, "[ARKADE] ERROR: dr_global_alloc failed during region table expansion.\n");
        dr_exit_process(1);
    }

    memcpy(new_regions, regions, sizeof(memory_region_t) * old_capacity);
    dr_global_free(regions, sizeof(memory_region_t) * old_capacity);

    regions = new_regions;

    // Link new slots into free list
    for (int i = old_capacity; i < new_capacity - 1; i++) {
        regions[i].next_free = i + 1;
    }
    regions[new_capacity - 1].next_free = -1;
    free_list_head = old_capacity;

    region_capacity = new_capacity;
}

int find_free_index() {
    #if 0
        struct timespec t = start_profile_section(&count_find_free_index);

        while (true) {
            for (int i = 0; i < region_capacity; ++i) {
                if (!regions[i].is_active) {
                    end_profile_section(t, &timer_find_free_index, count_find_free_index, FUNC_CALL_TRIGGER_THRESHOLD);
                    //dr_fprintf(STDOUT, "region_capacity = %d\n", region_capacity);

                    return i;
                }
            }

            expand_region_table();
        }

        end_profile_section(t, &timer_find_free_index, count_find_free_index, FUNC_CALL_TRIGGER_THRESHOLD);
        return -1;
    #else
        struct timespec t = start_profile_section(&count_find_free_index);

        if (free_list_head == -1) {
            expand_region_table();
        }

        int index = free_list_head;
        free_list_head = regions[index].next_free;

        end_profile_section(t, &timer_find_free_index, count_find_free_index, FUNC_CALL_TRIGGER_THRESHOLD);
        return index;
    #endif
}

// Initialize the hash table
void init_hash_table() {
    hash_table = NULL; // uthash uses NULL initialization
}

// Insert a new key-value pair into the hash table
void hash_table_insert(void *key, int value, size_t size, bool from_calloc, bool from_realloc) {

    HashKey hkey = { .pid = getpid(), .ptr = key };

    // Check if the same key was already registered before.
    HashEntry *existing = NULL;

    HASH_FIND(hh, hash_table, &hkey, sizeof(HashKey), existing);

    if (existing != NULL && existing->size == size) {
        dr_fprintf(STDOUT, "[WARN] Duplicate insert blocked for ptr (%p), pid(%d), size(%zu) (new index = %u, existing index = %d)\n",
                   hkey.ptr, hkey.pid, size, value, existing->value);

        if (from_calloc) {
            dr_fprintf(STDOUT, "[WARN] Duplicate insert caused by calloc-internal malloc\n");
        } else if (from_realloc) {
            dr_fprintf(STDOUT, "[WARN] Duplicate insert caused by realloc-internal malloc\n");
        } else {
            dr_fprintf(STDOUT, "[ERR] Duplicate insert caused by user-level malloc\n");
        }

        return;
    }

    HashEntry *entry = (HashEntry *)dr_global_alloc(sizeof(HashEntry));

    if (entry == NULL) {
        dr_fprintf(STDERR, "[ERROR] hash_table_insert: dr_global_alloc failed for key %p, value %u\n", key, value);
        return; // or handle gracefully (e.g., fallback, increment failure count, etc.)
    }

    entry->key = hkey;
    entry->value = value;
    entry->size = size;
    HASH_ADD(hh, hash_table, key, sizeof(HashKey), entry);

    dr_fprintf(STDOUT, "[DEBUG] HASH_COUNT after insert: %u\n", HASH_COUNT(hash_table));


    dr_fprintf(STDOUT, "[INFO] Current Hash Table Contents:\n");

    HashEntry *e, *tmp;
    HASH_ITER(hh, hash_table, e, tmp) {
        dr_fprintf(STDOUT, "    ptr = %p, pid = %d, size = %zu, value = %u\n", e->key.ptr, e->key.pid, e->size, e->value);
    }

    dr_fprintf(STDOUT, "[INFO] End of Hash Table Dump\n\n");
}

// Delete  from the hash table
void hash_table_delete(void *key, size_t size) {
    HashKey hkey = { .pid = getpid(), .ptr = key };

    HashEntry *entry = NULL;
    HASH_FIND(hh, hash_table, &hkey, sizeof(HashKey), entry);

    if (entry != NULL) {
        if (entry->size == size) {
            HASH_DEL(hash_table, entry);
            dr_global_free(entry, sizeof(HashEntry));
        } else {
            dr_fprintf(STDERR, "Same return address with different size is detected in the hashtable.\n");
        }
    }

    dr_fprintf(STDOUT, "[DEBUG] HASH_COUNT after delete: %u\n", HASH_COUNT(hash_table));
}

// Lookup a key in the hash table
static int hash_table_lookup(void *key) {
    HashKey hkey = { .pid = getpid(), .ptr = key };

    HashEntry *entry = NULL;
    HASH_FIND(hh, hash_table, &hkey, sizeof(HashKey), entry);

    if (entry != NULL) {
        return entry->value;
    }
    return -1; // not found
}

// Hybrid fallback version of free region lookup
static int lookup_region_index(void *ptr, bool *fast_hit) {
    // First, try the hash table lookup (fast path)
    int index = hash_table_lookup(ptr);

    if (index >= 0 && index < region_capacity) {
        memory_region_t *region = &regions[index];

        if (region->is_active &&
            region->pid == getpid() &&
            region->base_address == ptr) {
            // Valid fast path hit

            *fast_hit = true;
            return index;
        }
    }

    // Fallback to full scan if lookup failed or invalid
    *fast_hit = false;

    for (int i = 0; i < region_capacity; i++) {
        if (regions[i].is_active &&
            regions[i].base_address == ptr &&
            regions[i].pid == getpid()) {
            return i;
        }
    }

    // Not found
    return -1;
}

static void wrap_malloc_post(void *wrapcxt, void *user_data) {
    struct timespec t = start_profile_section(&count_wrap_malloc_post);

    dr_mutex_lock(mutex);

    void *ptr = (void *)drwrap_get_retval(wrapcxt);

    void *drcontext = drwrap_get_drcontext(wrapcxt);
    per_thread_t *data = (per_thread_t *)drmgr_get_tls_field(drcontext, tls_idx);
    size_t size = data->size; // Obtain the size saved in wrap_malloc_pre
    bool from_calloc = data->from_calloc;
    bool from_realloc = data->from_realloc;

    app_pc target = drwrap_get_func(wrapcxt);

    dr_fprintf(STDOUT, "[wrap_alloc_post] target=%p, malloc=%p, calloc=%p, realloc=%p, free=%p, return_addr=%p, size=%zu\n",
               target, malloc_func, calloc_func, realloc_func, free_func, ptr, size);

    //bool is_user = is_user_malloc(dr_get_current_drcontext(), wrapcxt);


    int index = find_free_index();

    if (index == -1) {
        //dr_fprintf(STDERR, "[OOM] Region table full. Total count = %d\n", region_count);
        dr_fprintf(STDERR, "[OOM] Region table full. Total count = %d\n", region_capacity);
	    dr_fprintf(STDERR, "[OOM]  Warning: memory region table full! malloc at %p of size %zu is not tracked.\n", ptr, size);

        end_profile_section(t, &timer_wrap_malloc_post, count_wrap_malloc_post, FUNC_CALL_TRIGGER_THRESHOLD);

        return;
    }

    regions[index].base_address = ptr;
    regions[index].size = size;
    regions[index].is_active = true;
    regions[index].pid = getpid();
    last_hit_index = index;

    //if (is_user) {
       //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "[ARKADE MALLOC RETURN] Malloc (User Code) return base address: %p, Size: %zu, Active: %s\n",
       //                                         regions[region_count].base_address,
       //                                         regions[region_count].size,
       //                                         regions[region_count].is_active ? "true" : "false");
    //} else {
       //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "[ARKADE MALLOC RETURN] Malloc (Nonuser Code) return base address: %p, Size: %zu, Active: %s\n",
       //                                         regions[region_count].base_address,
       //                                         regions[region_count].size,
       //                                         regions[region_count].is_active ? "true" : "false");
    //}

    // Insert into hash table
    hash_table_insert(ptr, index, size, from_calloc, from_realloc);

    dr_mutex_unlock(mutex);

    end_profile_section(t, &timer_wrap_malloc_post, count_wrap_malloc_post, FUNC_CALL_TRIGGER_THRESHOLD);
}

static void wrap_free_pre(void *wrapcxt, OUT void **user_data) {
    struct timespec t = start_profile_section(&count_wrap_free_pre);

    dr_mutex_lock(mutex);

    void *ptr = (void *)drwrap_get_arg(wrapcxt, 0);
    //bool is_user = is_user_malloc(dr_get_current_drcontext(), wrapcxt);
    bool double_free = 1;
    bool fast_hit = false;

    app_pc target = drwrap_get_func(wrapcxt);

    dr_fprintf(STDOUT, "[wrap_free_pre] target=%p, malloc=%p, calloc=%p, realloc=%p, free=%p, return_addr=%p\n",
               target, malloc_func, calloc_func, realloc_func, free_func, ptr);

    int index = lookup_region_index(ptr, &fast_hit);


    if (index >= 0) {
        //if (is_user) {
           //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "[ARKADE FREE] Free (User Code) (%p)\n", ptr);
        //} else {
           //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "[ARKADE FREE] Free (Nonuser Code) (%p)\n", ptr);
        //}

        regions[index].is_active = false;
        regions[index].next_free = free_list_head;
        free_list_head = index;

        if(fast_hit) {
            hash_table_delete(ptr, regions[index].size);

            //int hash_idx = hash_table_lookup(ptr);
            //if (hash_idx == index && regions[index].base_address == ptr) {
            //    hash_table_delete(ptr);
            //}
        }

        double_free = 0;

        if (last_hit_index == index) last_hit_index = -1;
    }
    dr_fprintf(STDOUT, "[wrap_free_pre] pid=%d, ptr=%p, size=%zu, index=%d\n", getpid(), ptr, regions[index].size, index);

//    void *return_addr = drwrap_get_retaddr(wrapcxt);
//    //drsym_info_t sym;
//    //memset(&sym, 0, sizeof(sym));
//    //sym.struct_size = sizeof(sym);
//    //sym.name = (char *)dr_global_alloc(256);
//    //sym.name_size = 256;
//    //sym.file = (char *)dr_global_alloc(256);
//    //sym.file_size = 256;
//
//    static module_data_t *last_mod_free = NULL;
//    module_data_t *mod = NULL;
//
//    if (last_mod_free != NULL &&
//        (app_pc)return_addr >= last_mod_free->start &&
//        (app_pc)return_addr < last_mod_free->end) {
//        mod = last_mod_free;
//    } else {
//        mod = dr_lookup_module(return_addr);
//        last_mod_free = mod;
//    }
//
    if (double_free == 0) {
//        if (mod != NULL) {
//           //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "[ARKADE FREE CALLED] Module start: %p\n", mod->start);
//           //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "[ARKADE FREE CALLED] Module end: %p\n", mod->end);
//           //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "[ARKADE FREE CALLED] Module full path: %s\n", mod->full_path);
//
//            size_t offset = (size_t)((app_pc)return_addr - mod->start);
//
//            //dr_log(NULL, DR_LOG_MASK_BASEOFFSET, "[ARKADE] Offset: %zu\n", offset);
//
//            /* ARKADE
//            drsym_error_t sym_res = drsym_lookup_address(mod->full_path, offset, &sym, DRSYM_DEFAULT_FLAGS);
//            dr_free_module_data(mod);
//            //if (sym_res == DRSYM_SUCCESS) {
//            if (sym_res == DRSYM_SUCCESS | sym_res == DRSYM_ERROR_LINE_NOT_AVAILABLE) {
//                if (is_user) {
//                   //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "[USER] Caller: %s (%s:%d)\n", sym.name, sym.file, sym.line);
//                } else {
//                   //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "Caller: %s (%s:%d)\n", sym.name, sym.file, sym.line);
//                }
//            } else {
//               //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 2, "Caller: Unknown, sym_res: %d\n", sym_res);
//            }
//            */
//        } else {
//           //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 2, "Caller: Unknown, mode: NULL\n");
//        }
    } else {
       //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 2, "[ARKADE FREE] Double Free detected\n");
        dr_fprintf(STDOUT, "[wrap_free_pre] double_free = %d is detected\n", double_free);
    }
//
//    //dr_global_free(sym.name, 256);
//    //dr_global_free(sym.file, 256);

    dr_mutex_unlock(mutex);
    end_profile_section(t, &timer_wrap_free_pre, count_wrap_free_pre, FUNC_CALL_TRIGGER_THRESHOLD);
}

reg_t get_register_value(dr_mcontext_t *mc, reg_id_t reg_id) {
    for (int i = 0; i < sizeof(reg_map) / sizeof(reg_map[0]); i++) {
        if (reg_map[i].reg_id == reg_id) {

            return *(reg_t *)((byte *)mc + reg_map[i].offset);
        }
    }
   //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 2, "[WARNING] Unhandled register: %s (reg_id: %d)\n", get_register_name(reg_id), reg_id);

    return 0;
}

static bool is_in_active_region(void *addr, memory_region_t **region_out, int print) {
    struct timespec t = start_profile_section(&count_is_in_active_region);

    if (last_hit_index >= 0 && last_hit_index < region_capacity) {
        memory_region_t *cached = &regions[last_hit_index];
        if (cached->is_active &&
            cached->pid == getpid() &&
            addr >= cached->base_address &&
            addr < (cached->base_address + cached->size)) {

            if (region_out) *region_out = cached;

            end_profile_section(t, &timer_is_in_active_region, count_is_in_active_region, FUNC_CALL_TRIGGER_THRESHOLD);
            return true;
        }
    }
    //for (int i = 0; i < region_count; i++) {
    for (int i = 0; i < region_capacity; i++) {
        if (regions[i].is_active &&
            regions[i].pid == getpid() &&
            addr >= regions[i].base_address &&
            addr < (regions[i].base_address + regions[i].size)) {

            last_hit_index = i;

            if (print) {
               //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "\t\tActual VA is within the allocated region\n");
               //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "\t\t\tActual VA: %p, Malloc Return Address: %p, Malloc Size: 0x%lx, Active: %d\n",
               //                                                 addr, regions[i].base_address, regions[i].size, regions[i].is_active);
            }

            if (region_out) {
                *region_out = &regions[i];
            }
            end_profile_section(t, &timer_is_in_active_region, count_is_in_active_region, FUNC_CALL_TRIGGER_THRESHOLD);

            return true;
        }
    }
   //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "\t\tActual VA: %p is beyond the allocated region\n\n", addr);

    end_profile_section(t, &timer_is_in_active_region, count_is_in_active_region, FUNC_CALL_TRIGGER_THRESHOLD);

    return false;
}

static void mem_access_callback(void *drcontext, app_pc instr_addr, app_pc abs_addr, app_pc rel_addr, int base_reg, int index_reg, int64_t scale, int64_t offset, int is_write) {

    int thread_id = dr_get_thread_id(drcontext);

   //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 4, "\t\tEntered mem_access_callback\n");
    app_pc mem_addr = NULL;
    reg_t base_reg_val = 0;
    reg_t index_reg_val = 0;

    //print_disassembled_pc(drcontext, instr_addr);

    if (base_reg != DR_REG_NULL) {
        dr_mcontext_t mc = { sizeof(mc), DR_MC_ALL };

        if (!dr_get_mcontext(drcontext, &mc)) {
           //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 2, "[ERROR] Failed to get register context at runtime!\n");
            return;
        }
       //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 4, "\n\t\tSuccessfully retrieved register context at runtime!.");
       //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 4, "\n\t\tAddress format: base + offset!.\n\n");

            base_reg_val = get_register_value(&mc, base_reg);

        if (index_reg != DR_REG_NULL) {
            index_reg_val = get_register_value(&mc, index_reg);
        }

        mem_addr = (app_pc)(base_reg_val + index_reg_val * scale + offset);

       //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "\t\t\tbase_reg: %s, base_addr = %p, index = %p, scale: %d, offset = 0x%lx, Final Address: %p\n\n", get_register_name(base_reg),
       //                                                                                                                        (void *)base_reg_val,
       //                                                                                                                        (void *)index_reg_val,
       //                                                                                                                        scale,
       //                                                                                                                        offset,
       //                                                                                                                        mem_addr);
    }
    else if (abs_addr != NULL) {

       //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 4, "\t\tAddress format: absolute address!.\n\n");
        mem_addr = abs_addr;
    }
    else if (rel_addr != NULL) {
        if (instr_addr != NULL) {

           //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 4, "\t\tAddress format: relative address!.\n\n");
            mem_addr = instr_addr + (ptr_int_t)rel_addr;
        }
       //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "\t\tProgram Counter is NULL.\n\n");
    }

   //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "\t\tCalculated memory address at runtime: %p\n", mem_addr);

    if (!is_in_active_region(mem_addr, NULL, 0)) {
        //dr_fprintf(STDOUT, "[DEBUG] Address %p is outside active malloc regions.\n", mem_addr);
        return;
    }


    memory_region_t *region;
    //app_pc addr = (app_pc)(base_reg_val + offset);
    app_pc addr = mem_addr;

    if (addr != NULL && is_in_active_region(addr, &region, 1)) {

        if ( base_reg_val == (reg_t)(region->base_address) ) {/*{{{*/
            pass_cnt++;
            debug_src_print = false;

            //print_disassembled_pc(drcontext, instr_addr, 3);

           //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "\n\t\t\t[RESULT] -> ");
           //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "[PASS] %s at Actual Addr: %p, Base Addr: %p, Index = %p, Scale: %d, Offset: 0x%lx, Malloc Ret Addr: %p, Malloc Size: 0x%lx\n",/*{{{*/
           //                     (is_write ? "WR" : "RD"), addr, (void *)base_reg_val, (void *)index_reg_val, scale, offset, region->base_address, region->size);/*}}}*/
        } else {
            test_pass = 0;/*{{{*/
            fail_cnt++;
            debug_src_print = true;

            //print_disassembled_pc(drcontext, instr_addr, 2);

           //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 2, "\n\t\t\t[RESULT] -> ");
           //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 2, "[FAIL] %s at Actual Addr: %p, Base Addr: %p, Malloc Ret Addr: %p\n",
           //                     (is_write ? "WR" : "RD"), addr, (void *)base_reg_val, region->base_address);/*}}}*/
        }

        dr_mcontext_t mcontext = { sizeof(mcontext), DR_MC_ALL };
        dr_get_mcontext(drcontext, &mcontext);

        //app_pc instr_addr = instr_get_app_pc(instr);}}}

        if (instr_addr != NULL ) {
            module_data_t *mod = dr_lookup_module(instr_addr);

            if (mod != NULL) {
                if (debug_src_print == true) {
                    size_t offset = (size_t)(instr_addr - mod->start);/*{{{*/

                    //drsym_info_t sym;
                    //memset(&sym, 0, sizeof(sym));
                    //sym.struct_size = sizeof(sym);
                    //sym.name = (char *)dr_global_alloc(256);
                    //sym.name_size = 256;
                    //sym.file = (char *)dr_global_alloc(256);
                    //sym.file_size = 256;


                    /* ARKADE
                    drsym_error_t sym_res = drsym_lookup_address(mod->full_path, offset, &sym, DRSYM_DEFAULT_FLAGS);
                    dr_free_module_data(mod);

                    //if (sym_res == DRSYM_SUCCESS || sym_res == DRSYM_ERROR_LINE_NOT_AVAILABLE) {
                    if (sym_res == DRSYM_SUCCESS) {
                       //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 2, "\t\t\t\t\t\tCaller: %s (%s:%d)\n\n", sym.name, sym.file, sym.line);
                    } else {
                       //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 2, "\t\t\t\t\t\tCaller: Unknown, sym_res: %d\n\n", sym_res);
                    }
                    */

                    //dr_global_free(sym.name, 256);
                    //dr_global_free(sym.file, 256);/*}}}*/
                }
            } else {
               //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 2, "\t\t\t\t\t\tModule lookup failed for instruction address: %p\n\n", instr_addr);
            }
        } else {
           //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 2, "\t\t\t\t\t\tInvalid instruction address: %p\n\n", instr_addr);
        }
    }
}

static bool should_ignore_memory_access(reg_id_t base_reg) {
    if (base_reg == DR_REG_NULL) {
       //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "\t\t\tbase_reg is DR_REG_NULL\n");
        return true;
    }
    //if (base_reg == DR_REG_RSP) {
    //   //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, "\t\t\tbase_reg is DR_REG_RSP\n");
    //    return true;
    //}
    //if (base_reg == DR_REG_RBP) {
    //   //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, "\t\t\tbase_reg is DR_REG_RBP\n");
    //    return true;
    //}
    //dr_log(NULL, DR_LOG_MASK_BASEOFFSET, "\t\t\tbase_reg has no issue\n");
    return false;
}

static void print_disassembled_pc(void *drcontext, app_pc instr_addr, int verbose) {
    char disasm_buf[256];
    int printed = 0;
    byte *pc = (byte *)instr_addr;

   //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "\t\tInstruction at PC %p: \n", instr_addr);
    //disassemble_with_info(drcontext, pc, STDOUT, true, true);
    disassemble_to_buffer(drcontext, pc, pc, true, true, disasm_buf, sizeof(disasm_buf), &printed);
   //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, verbose, "%s", disasm_buf);
}

static void print_disassembled_instr(void *drcontext, instr_t *instr, int verbose) {
    char disasm_buf[256];

   //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, verbose, "\tInstruction: ");
    instr_disassemble_to_buffer(drcontext, instr, disasm_buf, sizeof(disasm_buf));
   //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, verbose, "%s\n", disasm_buf);
    //instr_disassemble(drcontext, instr, STDERR);
}

static void print_disassembled_opnd(void *drcontext, opnd_t opnd, int verbose) {
    char opnd_buf[256];

   //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, verbose, "\t\tOperand: ");
    opnd_disassemble_to_buffer(drcontext, opnd, opnd_buf, sizeof(opnd_buf));
   //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, verbose, "%s ", opnd_buf);
}

static dr_emit_flags_t event_bb_insert(void *drcontext, void *tag, instrlist_t *bb, bool for_trace, bool translating, void **user_data) {
   //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "\n\n\n\n");
   //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "[ARKADE BB START] Basic Block is detected -> event_bb_insert is called.\n\n");

    for (instr_t *instr = instrlist_first(bb); instr != NULL; instr = instr_get_next(instr)) {

        //dr_log(NULL, DR_LOG_MASK_BASEOFFSET, "Raw instruction sequences: ");

        app_pc abs_addr= NULL;
        app_pc rel_addr= NULL;
        int64_t scale = 0;
        int64_t offset = 0;
        reg_id_t base_reg = DR_REG_NULL;
        reg_id_t index_reg = DR_REG_NULL;

        //print_disassembled_instr(drcontext, instr);

        // Skip non-memory access instruction
        if ( !(instr_reads_memory(instr) | instr_writes_memory(instr)) ) {
            //print_disassembled_instr(drcontext, instr, 3);
           //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "\t\tMemory access doesn't occur.\n\n");
            continue;
        }

        // Instruction is memory read
        if ( instr_reads_memory(instr) ) {
            for (int i = 0; i < instr_num_srcs(instr); i++) {
                opnd_t opnd = instr_get_src(instr, i);

                // Check if the given instruction is memory reference
                if ( !opnd_is_memory_reference(opnd) ) {
                    //print_disassembled_instr(drcontext, instr, 3);
                    //print_disassembled_opnd(drcontext, opnd, 3);
                   //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "is not a memory reference\n\n");
                    continue;
                }
                //ARKADE print_disassembled_instr(drcontext, instr, 3);
                //ARKADE print_disassembled_opnd(drcontext, opnd, 3);
                //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "is a read memory reference\n\n");

                if (opnd_is_base_disp(opnd)) {
                    base_reg = opnd_get_base(opnd);
                    index_reg = opnd_get_index(opnd);
                    scale = opnd_get_scale(opnd);
                    offset = opnd_get_disp(opnd);

                    if (should_ignore_memory_access(base_reg)) {
                        continue;
                    }
                }
                else if (opnd_is_abs_addr(opnd)) {
                    abs_addr = opnd_get_addr(opnd);
                }
                else if (opnd_is_rel_addr(opnd)) {
                    rel_addr = opnd_get_addr(opnd);
                }
                else {
                   //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 2, "[WARNING] Unsupported operand type. Skipping.\n");
                    continue;
                }

                app_pc instr_addr = instr_get_app_pc(instr);

               //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "\t[RD] mem_access_callback is registered to dr_insert_clean_call\n\n");
               // dr_insert_clean_call(drcontext, bb, instr, (void *)mem_access_callback, false, 9,
               //                                                                                OPND_CREATE_INTPTR(drcontext),
               //                                                                                OPND_CREATE_INTPTR(instr_addr),
               //                                                                                OPND_CREATE_INTPTR(abs_addr),
               //                                                                                OPND_CREATE_INTPTR(rel_addr),
               //                                                                                OPND_CREATE_INT32(base_reg),
               //                                                                                OPND_CREATE_INT32(index_reg),
               //                                                                                OPND_CREATE_INT64(scale),
               //                                                                                OPND_CREATE_INT64(offset),
               //                                                                                OPND_CREATE_INT32(0));  // read (is_write = 0)
            }
        }
        // Instruction is memory write
        if ( instr_writes_memory(instr) ) {
            for (int i = 0; i < instr_num_dsts(instr); i++) {
                opnd_t opnd = instr_get_dst(instr, i);

                // Check if the given instruction is memory reference
                if ( !opnd_is_memory_reference(opnd) ) {
                    //print_disassembled_instr(drcontext, instr, 3);
                    //print_disassembled_opnd(drcontext, opnd, 3);
                   //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "is not a memory reference\n\n");
                    continue;
                }
                //ARKADE print_disassembled_instr(drcontext, instr, 3);
                //ARKADE print_disassembled_opnd(drcontext, opnd, 3);
                //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "is a write memory reference\n\n");

                if (opnd_is_base_disp(opnd)) {
                    base_reg = opnd_get_base(opnd);
                    index_reg = opnd_get_index(opnd);
                    scale = opnd_get_scale(opnd);
                    offset = opnd_get_disp(opnd);

                   //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "\t\t\t[base + offset] offset = 0x%lx\n", offset);
                    if (should_ignore_memory_access(base_reg)) {
                        continue;
                    }
                }
                else if (opnd_is_abs_addr(opnd)) {
                    abs_addr = opnd_get_addr(opnd);
                   //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "\t\t\t[absolute address] offset = 0x%lx\n", offset);
                }
                else if (opnd_is_rel_addr(opnd)) {
                    rel_addr = opnd_get_addr(opnd);
                   //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "\t\t\t[relative address] offset = 0x%lx\n", offset);
                }
                else {
                   //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 2, "[WARNING] Unsupported operand type. Skipping.\n");
                    continue;
                }

                app_pc instr_addr = instr_get_app_pc(instr);

               //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "\t[WR] mem_access_callback is registered to dr_insert_clean_call\n\n");
               // dr_insert_clean_call(drcontext, bb, instr, (void *)mem_access_callback, false, 9,
               //                                                                                OPND_CREATE_INTPTR(drcontext),
               //                                                                                OPND_CREATE_INTPTR(instr_addr),
               //                                                                                OPND_CREATE_INTPTR(abs_addr),
               //                                                                                OPND_CREATE_INTPTR(rel_addr),
               //                                                                                OPND_CREATE_INT32(base_reg),
               //                                                                                OPND_CREATE_INT32(index_reg),
               //                                                                                OPND_CREATE_INT64(scale),
               //                                                                                OPND_CREATE_INT64(offset),
               //                                                                                OPND_CREATE_INT32(1));  // write (is_write = 1)
            }
        }
    }

    return DR_EMIT_DEFAULT;
}

static void report_test_result(void) {
    if (test_pass == 1) {
      //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "PASS: %s\n", "All memory accesses are based on (base + offset) scheme.");
    } else {
      //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 2, "FAIL: %s\n", "Some memory accesses are NOT based on (base + offset) scheme.");
    }
    dr_fprintf(STDOUT, "Pass count: %llu, Fail count: %llu \n", pass_cnt, fail_cnt);
    //dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 1, "Pass count: %llu, Fail count: %llu \n", pass_cnt, fail_cnt);
}

static void module_load_event(void *drcontext, const module_data_t *mod, bool loaded) {

    app_pc malloc_towrap  = (app_pc)dr_get_proc_address(mod->handle, MALLOC_ROUTINE_NAME);
    app_pc calloc_towrap  = (app_pc)dr_get_proc_address(mod->handle, CALLOC_ROUTINE_NAME);
    app_pc realloc_towrap = (app_pc)dr_get_proc_address(mod->handle, REALLOC_ROUTINE_NAME);
    app_pc free_towrap = (app_pc)dr_get_proc_address(mod->handle, FREE_ROUTINE_NAME);

    //dr_fprintf(STDOUT, "[module_load_event 1] malloc_towrap=%p, calloc_towrap=%p, realloc_towrap=%p\n",
    //                    malloc_towrap, calloc_towrap, realloc_towrap);

    if (malloc_towrap != NULL) {
        if (drwrap_wrap(malloc_towrap, wrap_malloc_pre, wrap_malloc_post)) {
           //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "\n[ARKADE WRAP MALLOC] Wrapped malloc successfully @ %p\n", malloc_towrap);
            malloc_func = malloc_towrap;
            //dr_fprintf(STDOUT, "[mod_load] module loaded: %s\n", mod->full_path);
            //dr_fprintf(STDOUT, "malloc_towrap is loaded (%p)\n", malloc_towrap);
        } else {
           //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "\n[ARKADE WRAP MALLOC] Failed to wrap malloc @ %p: already wrapped?\n", malloc_towrap);
        }
    }

    if (calloc_towrap != NULL) {
        if (drwrap_wrap(calloc_towrap, wrap_malloc_pre, wrap_malloc_post)) {
           //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "\n[ARKADE WRAP MALLOC] Wrapped calloc successfully @ %p\n", calloc_towrap);
            calloc_func = calloc_towrap;
            //dr_fprintf(STDOUT, "[mod_load] module loaded: %s\n", mod->full_path);
            //dr_fprintf(STDOUT, "calloc_towrap is loaded (%p)\n", calloc_towrap);
        } else {
           //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "\n[ARKADE WRAP MALLOC] Failed to wrap calloc @ %p: already wrapped?\n", calloc_towrap);
        }
    }

    if (realloc_towrap != NULL) {
        if (drwrap_wrap(realloc_towrap, wrap_malloc_pre, wrap_malloc_post)) {
           //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "\n[ARKADE WRAP MALLOC] Wrapped realloc successfully @ %p\n", realloc_towrap);
            realloc_func = realloc_towrap;
            //dr_fprintf(STDOUT, "[mod_load] module loaded: %s\n", mod->full_path);
            //dr_fprintf(STDOUT, "realloc_towrap is loaded (%p)\n", realloc_towrap);
        } else {
           //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "\n[ARKADE WRAP MALLOC] Failed to wrap realloc @ %p: already wrapped?\n", realloc_towrap);
        }
    }

    if (free_towrap != NULL) {
        if (drwrap_wrap(free_towrap, wrap_free_pre, NULL)) {
           //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE WRAP FREE] Wrapped free successfully @ %p\n", free_towrap);
            free_func = free_towrap;
            //dr_fprintf(STDOUT, "[mod_load] module loaded: %s\n", mod->full_path);
            //dr_fprintf(STDOUT, "free_towrap is loaded (%p)\n", free_towrap);
        } else {
           //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE WRAP FREE] Failed to wrap free @ %p: already wrapped?\n", free_towrap);
        }
    }

    //dr_fprintf(STDOUT, "[module_load_event 2] malloc_towrap=%p, calloc_towrap=%p, realloc_towrap=%p\n",
    //                    malloc_towrap, calloc_towrap, realloc_towrap);
}

static void event_thread_init(void *drcontext) {
    per_thread_t *data = dr_thread_alloc(drcontext, sizeof(per_thread_t));
    DR_ASSERT(data != NULL);
    drmgr_set_tls_field(drcontext, tls_idx, data);

    data->log = log_file_open(client_id, drcontext, NULL, "arkade_memtrace_base_offset.log",
                              DR_FILE_CLOSE_ON_FORK | DR_FILE_ALLOW_LARGE);
    data->logf = log_stream_from_file(data->log);
}

static void event_thread_exit(void *drcontext) {
    per_thread_t *data = drmgr_get_tls_field(drcontext, tls_idx);
    log_stream_close(data->logf); /* closes fd too */
    dr_thread_free(drcontext, data, sizeof(per_thread_t));
}

static void event_exit(void) {
    if (!drmgr_unregister_tls_field(tls_idx) ||
        !drmgr_unregister_thread_init_event(event_thread_init) ||
        !drmgr_unregister_thread_exit_event(event_thread_exit) ||
        !drmgr_unregister_module_load_event(module_load_event))
        DR_ASSERT(false);

    dr_mutex_destroy(mutex);

    drwrap_exit();
   //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE EXIT 1] drwrap_exit is done.\n");

    drmgr_exit();
   //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE EXIT 2] drmgr_exit is done.\n");

    drsym_exit();
   //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE EXIT 2] drsym_exit is done.\n");

    drutil_exit();
   //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE EXIT 3] drutil_exit is done.\n");

    drreg_exit();
   //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE EXIT 4] drreg_exit is done.\n");

    report_test_result();
    //report_function_timing();
}

DR_EXPORT void dr_client_main(client_id_t id, int argc, const char *argv[]) {
   //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE INIT 1] Client initialization starts.\n");

    if ( drmgr_init() ) {
       //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE INIT 2] drmgr_init is done.\n");
    } else {
       //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE INIT 2] drmgr_init is NOT properly done.\n");
        DR_ASSERT(false);
    }

    if ( drutil_init() ) {
       //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE INIT 3] drutil_init is done.\n");
    } else {
       //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE INIT 3] drutil_init is NOT properly done.\n");
        DR_ASSERT(false);
    }

    drreg_options_t ops = { sizeof(drreg_options_t), 3, false };
    drreg_status_t result = drreg_init(&ops);
    if ( result == DRREG_SUCCESS ) {
       //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE INIT 4] drreg_init is done.\n");
    } else {
       //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE INIT 4] drreg_init is NOT properly done.\n");
        DR_ASSERT(false);
    }

    if ( drwrap_init() ) {
       //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE INIT 5] drwrap_init is done.\n");
    } else {
       //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE INIT 5] drwrap_init is NOT properly done.\n");
        DR_ASSERT(false);
    }

    if ( drsym_init(0) == DRSYM_SUCCESS ) {
       //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE INIT 6] drsym_init is done.\n");
    } else {
       //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE INIT 6] drsym_init is NOT properly done.\n");
        DR_ASSERT(false);
    }

    init_region_table();
    init_hash_table();

    client_id = id;
    mutex = dr_mutex_create();

    dr_register_exit_event(event_exit);
    drmgr_register_thread_init_event(event_thread_init);
    drmgr_register_thread_exit_event(event_thread_exit);
    drmgr_register_module_load_event(module_load_event);
   //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE INIT 7] module_load_event registration is done\n");

    drmgr_register_bb_instrumentation_event(event_bb_insert, NULL, NULL);
   //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE INIT 8] BB(Basic Block) insertion is done\n\n");

    tls_idx = drmgr_register_tls_field();
    DR_ASSERT(tls_idx != -1);

   //ARKADE dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 2, "Client 'memtrace' initializing\n");
}
