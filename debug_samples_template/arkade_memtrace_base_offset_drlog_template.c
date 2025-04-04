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
//#include "core/ir/opnd.h"

#define MAX_REGIONS 1024
#define MALLOC_ROUTINE_NAME "malloc"
#define FREE_ROUTINE_NAME "free"

#define DR_LOG_MASK_BASEOFFSET 0x80000000

#ifndef OUT
#define OUT
#endif

typedef struct _memory_region_t {
    void *base_address;
    size_t size;
    bool is_active;
} memory_region_t;

typedef struct {
    file_t log;
    FILE *logf;
    size_t size;
} per_thread_t;

typedef struct {
    reg_id_t reg_id;
    size_t offset;
} reg_map_t;

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


static memory_region_t regions[MAX_REGIONS];
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

static void event_thread_init(void *drcontext);
static void event_thread_exit(void *drcontext);
static void event_exit(void);
static void module_load_event(void *drcontext, const module_data_t *mod, bool loaded);
static void print_disassembled_instr(void *drcontext, instr_t *instr, int verbose);
static void print_disassembled_pc(void *drcontext, app_pc instr_addr, int verbose);

static bool should_ignore_memory_access(reg_id_t base_reg);

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
        bool is_user = (strstr(mod->full_path, "/home/arkade/tools/Binary_Instrumentation_Tools/DynamoRIO/src/github/dynamorio/debug/arkade_examples/hello2") != NULL);
        dr_free_module_data(mod);
        return is_user;
    }
    return false;
}

static void wrap_malloc_pre(void *wrapcxt, OUT void **user_data) {
    size_t size = (size_t)drwrap_get_arg(wrapcxt, 0);

    void *drcontext = drwrap_get_drcontext(wrapcxt);
    per_thread_t *data = (per_thread_t *)drmgr_get_tls_field(drcontext, tls_idx);
    data->size = size; // Pass 'size' to wrap_malloc_post

    bool is_user = is_user_malloc(dr_get_current_drcontext(), wrapcxt);

    if (is_user) {
        dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 1, "[ARKADE MALLOC CALLED] Malloc (User Code) (size: %zu)\n", size);
    } else {
        dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 1, "[ARKADE MALLOC CALLED] Malloc (Nonuser Code) (size: %zu)\n", size);
    }

    void *return_addr = drwrap_get_retaddr(wrapcxt);
    drsym_info_t sym;
    memset(&sym, 0, sizeof(sym));
    sym.struct_size = sizeof(sym);
    sym.name = (char *)dr_global_alloc(256);
    sym.name_size = 256;
    sym.file = (char *)dr_global_alloc(256);
    sym.file_size = 256;

    module_data_t *mod = dr_lookup_module(return_addr);
    if (mod != NULL) {
        dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "[ARKADE MALLOC CALLED] Module start: %p\n", mod->start);
        dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "[ARKADE MALLOC CALLED] Module end: %p\n", mod->end);
        dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "[ARKADE MALLOC CALLED] Module full path: %s\n", mod->full_path);

        size_t offset = (size_t)((app_pc)return_addr - mod->start);

        //dr_fprintf(STDOUT, "[ARKADE] Offset: %zu\n", offset);

        drsym_error_t sym_res = drsym_lookup_address(mod->full_path, offset, &sym, DRSYM_DEFAULT_FLAGS);
        dr_free_module_data(mod);
        if (sym_res == DRSYM_SUCCESS) {
        //if (sym_res == DRSYM_SUCCESS | sym_res == DRSYM_ERROR_LINE_NOT_AVAILABLE) {
            if (is_user) {
                dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "[ARKADE MALLOC CALLED] Caller (User Code): %s (%s:%d)\n", sym.name, sym.file, sym.line);
            } else {
                dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "[ARKADE MALLOC CALLED] Caller (Nonuser Code): %s (%s:%d)\n", sym.name, sym.file, sym.line);
            }
        } else {
            dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 1, "[ARKADE MALLOC CALLED] Caller: Unknown, sym_res: %d\n", sym_res);
        }
    } else {
        dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 1, "[ARKADE MALLOC CALLED] Caller: Unknown, mode: NULL\n");
    }

    dr_global_free(sym.name, 256);
    dr_global_free(sym.file, 256);
}

static void wrap_malloc_post(void *wrapcxt, void *user_data) {
    void *ptr = (void *)drwrap_get_retval(wrapcxt);

    void *drcontext = drwrap_get_drcontext(wrapcxt);
    per_thread_t *data = (per_thread_t *)drmgr_get_tls_field(drcontext, tls_idx);
    size_t size = data->size; // Obtain the size saved in wrap_malloc_pre

    bool is_user = is_user_malloc(dr_get_current_drcontext(), wrapcxt);

    if (region_count < MAX_REGIONS) {
        regions[region_count].base_address = ptr;
        regions[region_count].size = size;
        regions[region_count].is_active = true;

        if (is_user) {
            dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "[ARKADE MALLOC RETURN] Malloc (User Code) return base address: %p, Size: %zu, Active: %s\n",
                                                    regions[region_count].base_address,
                                                    regions[region_count].size,
                                                    regions[region_count].is_active ? "true" : "false");
        } else {
            dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "[ARKADE MALLOC RETURN] Malloc (Nonuser Code) return base address: %p, Size: %zu, Active: %s\n",
                                                    regions[region_count].base_address,
                                                    regions[region_count].size,
                                                    regions[region_count].is_active ? "true" : "false");
        }

        region_count++;
    }
}

static void wrap_free_pre(void *wrapcxt, OUT void **user_data) {
    void *ptr = (void *)drwrap_get_arg(wrapcxt, 0);
    bool is_user = is_user_malloc(dr_get_current_drcontext(), wrapcxt);
    bool double_free = 1;

    for (int i = 0; i < region_count; i++) {
        if (regions[i].base_address == ptr && regions[i].is_active) {
            if (is_user) {
                dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "[ARKADE FREE] Free (User Code) (%p)\n", ptr);
            } else {
                dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "[ARKADE FREE] Free (Nonuser Code) (%p)\n", ptr);
            }

            regions[i].is_active = false;
            double_free = 0;

            break;
        }
    }

    void *return_addr = drwrap_get_retaddr(wrapcxt);
    drsym_info_t sym;
    memset(&sym, 0, sizeof(sym));
    sym.struct_size = sizeof(sym);
    sym.name = (char *)dr_global_alloc(256);
    sym.name_size = 256;
    sym.file = (char *)dr_global_alloc(256);
    sym.file_size = 256;

    module_data_t *mod = dr_lookup_module(return_addr);

    if (double_free == 0) {
        if (mod != NULL) {
            dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "[ARKADE FREE CALLED] Module start: %p\n", mod->start);
            dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "[ARKADE FREE CALLED] Module end: %p\n", mod->end);
            dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "[ARKADE FREE CALLED] Module full path: %s\n", mod->full_path);

            size_t offset = (size_t)((app_pc)return_addr - mod->start);

            //dr_fprintf(STDOUT, "[ARKADE] Offset: %zu\n", offset);

            drsym_error_t sym_res = drsym_lookup_address(mod->full_path, offset, &sym, DRSYM_DEFAULT_FLAGS);
            dr_free_module_data(mod);
            //if (sym_res == DRSYM_SUCCESS) {
            if (sym_res == DRSYM_SUCCESS | sym_res == DRSYM_ERROR_LINE_NOT_AVAILABLE) {
                if (is_user) {
                    dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "[USER] Caller: %s (%s:%d)\n", sym.name, sym.file, sym.line);
                } else {
                    dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "Caller: %s (%s:%d)\n", sym.name, sym.file, sym.line);
                }
            } else {
                dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 1, "Caller: Unknown, sym_res: %d\n", sym_res);
            }
        } else {
            dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 1, "Caller: Unknown, mode: NULL\n");
        }
    } else {
        dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 1, "[ARKADE FREE] Double Free detected\n");
    }

    dr_global_free(sym.name, 256);
    dr_global_free(sym.file, 256);
}

reg_t get_register_value(dr_mcontext_t *mc, reg_id_t reg_id) {
    for (int i = 0; i < sizeof(reg_map) / sizeof(reg_map[0]); i++) {
        if (reg_map[i].reg_id == reg_id) {

            return *(reg_t *)((byte *)mc + reg_map[i].offset);
        }
    }
    dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 1, "[WARNING] Unhandled register: %s (reg_id: %d)\n", get_register_name(reg_id), reg_id);

    return 0;
}

static bool is_in_active_region(void *addr, memory_region_t **region_out, int print) {
    for (int i = 0; i < region_count; i++) {
        if (regions[i].is_active &&
            addr >= regions[i].base_address &&
            addr < (regions[i].base_address + regions[i].size)) {

            if (print) {
                dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "\t\tActual VA is within the allocated region\n");
                dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "\t\t\tActual VA: %p, Malloc Return Address: %p, Malloc Size: 0x%lx, Active: %d\n",
                                                                addr, regions[i].base_address, regions[i].size, regions[i].is_active);
            }

            if (region_out) {
                *region_out = &regions[i];
            }
            return true;
        }
    }
    dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "\t\tActual VA: %p is beyond the allocated region\n\n", addr);

    return false;
}

static void mem_access_callback(void *drcontext, app_pc instr_addr, app_pc abs_addr, app_pc rel_addr, int base_reg, int index_reg, int64_t scale, int64_t offset, int is_write) {

    int thread_id = dr_get_thread_id(drcontext);

    dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 4, "\t\tEntered mem_access_callback\n");
    app_pc mem_addr = NULL;
    reg_t base_reg_val = 0;
    reg_t index_reg_val = 0;

    //print_disassembled_pc(drcontext, instr_addr);

    if (base_reg != DR_REG_NULL) {
        dr_mcontext_t mc = { sizeof(mc), DR_MC_ALL };

        if (!dr_get_mcontext(drcontext, &mc)) {
            dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 1, "[ERROR] Failed to get register context at runtime!\n");
            return;
        }
        dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 4, "\n\t\tSuccessfully retrieved register context at runtime!.");
        dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 4, "\n\t\tAddress format: base + offset!.\n\n");

            base_reg_val = get_register_value(&mc, base_reg);

        if (index_reg != DR_REG_NULL) {
            index_reg_val = get_register_value(&mc, index_reg);
        }

        mem_addr = (app_pc)(base_reg_val + index_reg_val * scale + offset);

        dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "\t\t\tbase_reg: %s, base_addr = %p, index = %p, scale: %d, offset = 0x%lx, Final Address: %p\n\n", get_register_name(base_reg),
                                                                                                                               (void *)base_reg_val,
                                                                                                                               (void *)index_reg_val,
                                                                                                                               scale,
                                                                                                                               offset,
                                                                                                                               mem_addr);
    }
    else if (abs_addr != NULL) {

        dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 4, "\t\tAddress format: absolute address!.\n\n");
        mem_addr = abs_addr;
    }
    else if (rel_addr != NULL) {
        if (instr_addr != NULL) {

            dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 4, "\t\tAddress format: relative address!.\n\n");
            mem_addr = instr_addr + (ptr_int_t)rel_addr;
        }
        dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "\t\tProgram Counter is NULL.\n\n");
    }

    dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "\t\tCalculated memory address at runtime: %p\n", mem_addr);

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

            print_disassembled_pc(drcontext, instr_addr, 3);

            dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "\n\t\t\t[RESULT] -> ");
            dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "[PASS] %s at Actual Addr: %p, Base Addr: %p, Index = %p, Scale: %d, Offset: 0x%lx, Malloc Ret Addr: %p, Malloc Size: 0x%lx\n",/*{{{*/
                                (is_write ? "WR" : "RD"), addr, (void *)base_reg_val, (void *)index_reg_val, scale, offset, region->base_address, region->size);/*}}}*/
        } else {
            test_pass = 0;/*{{{*/
            fail_cnt++;
            debug_src_print = true;

            print_disassembled_pc(drcontext, instr_addr, 1);

            dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 1, "\n\t\t\t[RESULT] -> ");
            dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 1, "[FAIL] %s at Actual Addr: %p, Base Addr: %p, Malloc Ret Addr: %p\n",
                                (is_write ? "WR" : "RD"), addr, (void *)base_reg_val, region->base_address);/*}}}*/
        }

        dr_mcontext_t mcontext = { sizeof(mcontext), DR_MC_ALL };
        dr_get_mcontext(drcontext, &mcontext);

        //app_pc instr_addr = instr_get_app_pc(instr);}}}

        if (instr_addr != NULL ) {
            module_data_t *mod = dr_lookup_module(instr_addr);

            if (mod != NULL) {
                if (debug_src_print == true) {
                    size_t offset = (size_t)(instr_addr - mod->start);/*{{{*/

                    drsym_info_t sym;
                    memset(&sym, 0, sizeof(sym));
                    sym.struct_size = sizeof(sym);
                    sym.name = (char *)dr_global_alloc(256);
                    sym.name_size = 256;
                    sym.file = (char *)dr_global_alloc(256);
                    sym.file_size = 256;


                    drsym_error_t sym_res = drsym_lookup_address(mod->full_path, offset, &sym, DRSYM_DEFAULT_FLAGS);
                    dr_free_module_data(mod);

                    //if (sym_res == DRSYM_SUCCESS || sym_res == DRSYM_ERROR_LINE_NOT_AVAILABLE) {
                    if (sym_res == DRSYM_SUCCESS) {
                        dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 1, "\t\t\t\t\t\tCaller: %s (%s:%d)\n\n", sym.name, sym.file, sym.line);
                    } else {
                        dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 1, "\t\t\t\t\t\tCaller: Unknown, sym_res: %d\n\n", sym_res);
                    }

                    dr_global_free(sym.name, 256);
                    dr_global_free(sym.file, 256);/*}}}*/
                }
            } else {
                dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 1, "\t\t\t\t\t\tModule lookup failed for instruction address: %p\n\n", instr_addr);
            }
        } else {
            dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 1, "\t\t\t\t\t\tInvalid instruction address: %p\n\n", instr_addr);
        }
    }
}

static bool should_ignore_memory_access(reg_id_t base_reg) {
    if (base_reg == DR_REG_NULL) {
        dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "\t\t\tbase_reg is DR_REG_NULL\n");
        return true;
    }
    //if (base_reg == DR_REG_RSP) {
    //    dr_fprintf(STDOUT, "\t\t\tbase_reg is DR_REG_RSP\n");
    //    return true;
    //}
    //if (base_reg == DR_REG_RBP) {
    //    dr_fprintf(STDOUT, "\t\t\tbase_reg is DR_REG_RBP\n");
    //    return true;
    //}
    //dr_fprintf(STDOUT, "\t\t\tbase_reg has no issue\n");
    return false;
}

static void print_disassembled_pc(void *drcontext, app_pc instr_addr, int verbose) {
    char disasm_buf[256];
    int printed = 0;
    byte *pc = (byte *)instr_addr;

    dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "\t\tInstruction at PC %p: \n", instr_addr);
    //disassemble_with_info(drcontext, pc, STDOUT, true, true);
    disassemble_to_buffer(drcontext, pc, pc, true, true, disasm_buf, sizeof(disasm_buf), &printed);
    dr_log(NULL, DR_LOG_MASK_BASEOFFSET, verbose, "%s", disasm_buf);
}

static void print_disassembled_instr(void *drcontext, instr_t *instr, int verbose) {
    char disasm_buf[256];

    dr_log(NULL, DR_LOG_MASK_BASEOFFSET, verbose, "\tInstruction: ");
    instr_disassemble_to_buffer(drcontext, instr, disasm_buf, sizeof(disasm_buf));
    dr_log(NULL, DR_LOG_MASK_BASEOFFSET, verbose, "%s\n", disasm_buf);
    //instr_disassemble(drcontext, instr, STDERR);
}

static void print_disassembled_opnd(void *drcontext, opnd_t opnd, int verbose) {
    char opnd_buf[256];

    dr_log(NULL, DR_LOG_MASK_BASEOFFSET, verbose, "\t\tOperand: ");
    opnd_disassemble_to_buffer(drcontext, opnd, opnd_buf, sizeof(opnd_buf));
    dr_log(NULL, DR_LOG_MASK_BASEOFFSET, verbose, "%s ", opnd_buf);
}

static dr_emit_flags_t event_bb_insert(void *drcontext, void *tag, instrlist_t *bb, bool for_trace, bool translating, void **user_data) {
    dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "\n\n\n\n");
    dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "[ARKADE BB START] Basic Block is detected -> event_bb_insert is called.\n\n");

    for (instr_t *instr = instrlist_first(bb); instr != NULL; instr = instr_get_next(instr)) {

        //dr_fprintf(STDOUT, "Raw instruction sequences: ");

        app_pc abs_addr= NULL;
        app_pc rel_addr= NULL;
        int64_t scale = 0;
        int64_t offset = 0;
        reg_id_t base_reg = DR_REG_NULL;
        reg_id_t index_reg = DR_REG_NULL;

        //print_disassembled_instr(drcontext, instr);

        // Skip non-memory access instruction
        if ( !(instr_reads_memory(instr) | instr_writes_memory(instr)) ) {
            print_disassembled_instr(drcontext, instr, 3);
            dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "\t\tMemory access doesn't occur.\n\n");
            continue;
        }

        // Instruction is memory read
        if ( instr_reads_memory(instr) ) {
            for (int i = 0; i < instr_num_srcs(instr); i++) {
                opnd_t opnd = instr_get_src(instr, i);

                // Check if the given instruction is memory reference
                if ( !opnd_is_memory_reference(opnd) ) {
                    print_disassembled_instr(drcontext, instr, 3);
                    print_disassembled_opnd(drcontext, opnd, 3);
                    dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "is not a memory reference\n\n");
                    continue;
                }
                print_disassembled_instr(drcontext, instr, 3);
                print_disassembled_opnd(drcontext, opnd, 3);
                dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "is a read memory reference\n\n");

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
                    dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 1, "[WARNING] Unsupported operand type. Skipping.\n");
                    continue;
                }

                app_pc instr_addr = instr_get_app_pc(instr);

                dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "\t[RD] mem_access_callback is registered to dr_insert_clean_call\n\n");
                dr_insert_clean_call(drcontext, bb, instr, (void *)mem_access_callback, false, 9,
                                                                                               OPND_CREATE_INTPTR(drcontext),
                                                                                               OPND_CREATE_INTPTR(instr_addr),
                                                                                               OPND_CREATE_INTPTR(abs_addr),
                                                                                               OPND_CREATE_INTPTR(rel_addr),
                                                                                               OPND_CREATE_INT32(base_reg),
                                                                                               OPND_CREATE_INT32(index_reg),
                                                                                               OPND_CREATE_INT64(scale),
                                                                                               OPND_CREATE_INT64(offset),
                                                                                               OPND_CREATE_INT32(0));  // read (is_write = 0)
            }
        }
        // Instruction is memory write
        if ( instr_writes_memory(instr) ) {
            for (int i = 0; i < instr_num_dsts(instr); i++) {
                opnd_t opnd = instr_get_dst(instr, i);

                // Check if the given instruction is memory reference
                if ( !opnd_is_memory_reference(opnd) ) {
                    print_disassembled_instr(drcontext, instr, 3);
                    print_disassembled_opnd(drcontext, opnd, 3);
                    dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "is not a memory reference\n\n");
                    continue;
                }
                print_disassembled_instr(drcontext, instr, 3);
                print_disassembled_opnd(drcontext, opnd, 3);
                dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "is a write memory reference\n\n");

                if (opnd_is_base_disp(opnd)) {
                    base_reg = opnd_get_base(opnd);
                    index_reg = opnd_get_index(opnd);
                    scale = opnd_get_scale(opnd);
                    offset = opnd_get_disp(opnd);

                    dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "\t\t\t[base + offset] offset = 0x%lx\n", offset);
                    if (should_ignore_memory_access(base_reg)) {
                        continue;
                    }
                }
                else if (opnd_is_abs_addr(opnd)) {
                    abs_addr = opnd_get_addr(opnd);
                    dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "\t\t\t[absolute address] offset = 0x%lx\n", offset);
                }
                else if (opnd_is_rel_addr(opnd)) {
                    rel_addr = opnd_get_addr(opnd);
                    dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "\t\t\t[relative address] offset = 0x%lx\n", offset);
                }
                else {
                    dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 1, "[WARNING] Unsupported operand type. Skipping.\n");
                    continue;
                }

                app_pc instr_addr = instr_get_app_pc(instr);

                dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "\t[WR] mem_access_callback is registered to dr_insert_clean_call\n\n");
                dr_insert_clean_call(drcontext, bb, instr, (void *)mem_access_callback, false, 9,
                                                                                               OPND_CREATE_INTPTR(drcontext),
                                                                                               OPND_CREATE_INTPTR(instr_addr),
                                                                                               OPND_CREATE_INTPTR(abs_addr),
                                                                                               OPND_CREATE_INTPTR(rel_addr),
                                                                                               OPND_CREATE_INT32(base_reg),
                                                                                               OPND_CREATE_INT32(index_reg),
                                                                                               OPND_CREATE_INT64(scale),
                                                                                               OPND_CREATE_INT64(offset),
                                                                                               OPND_CREATE_INT32(1));  // write (is_write = 1)
            }
        }
    }

    return DR_EMIT_DEFAULT;
}

static void report_test_result(void) {
    if (test_pass == 1) {
       dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 3, "PASS: %s\n", "All memory accesses are based on (base + offset) scheme.");
    } else {
       dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 1, "FAIL: %s\n", "Some memory accesses are NOT based on (base + offset) scheme.");
    }
    dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 1, "Pass count: %llu, Fail count: %llu \n", pass_cnt, fail_cnt);
}

static void module_load_event(void *drcontext, const module_data_t *mod, bool loaded) {
    app_pc malloc_towrap = (app_pc)dr_get_proc_address(mod->handle, MALLOC_ROUTINE_NAME);
    app_pc free_towrap = (app_pc)dr_get_proc_address(mod->handle, FREE_ROUTINE_NAME);

    if (malloc_towrap != NULL) {
        if (drwrap_wrap(malloc_towrap, wrap_malloc_pre, wrap_malloc_post)) {
            dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "\n[ARKADE WRAP MALLOC] Wrapped malloc successfully @ %p\n", malloc_towrap);
        } else {
            dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "\n[ARKADE WRAP MALLOC] Failed to wrap malloc @ %p: already wrapped?\n", malloc_towrap);
        }
    }

    if (free_towrap != NULL) {
        if (drwrap_wrap(free_towrap, wrap_free_pre, NULL)) {
            dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE WRAP FREE] Wrapped free successfully @ %p\n", free_towrap);
        } else {
            dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE WRAP FREE] Failed to wrap free @ %p: already wrapped?\n", free_towrap);
        }
    }
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
    dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE EXIT 1] drwrap_exit is done.\n");

    drmgr_exit();
    dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE EXIT 2] drmgr_exit is done.\n");

    drsym_exit();
    dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE EXIT 2] drsym_exit is done.\n");

    drutil_exit();
    dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE EXIT 3] drutil_exit is done.\n");

    drreg_exit();
    dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE EXIT 4] drreg_exit is done.\n");

    report_test_result();
}

DR_EXPORT void dr_client_main(client_id_t id, int argc, const char *argv[]) {
    dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE INIT 1] Client initialization starts.\n");

    if ( drmgr_init() ) {
        dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE INIT 2] drmgr_init is done.\n");
    } else {
        dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE INIT 2] drmgr_init is NOT properly done.\n");
        DR_ASSERT(false);
    }

    if ( drutil_init() ) {
        dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE INIT 3] drutil_init is done.\n");
    } else {
        dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE INIT 3] drutil_init is NOT properly done.\n");
        DR_ASSERT(false);
    }

    drreg_options_t ops = { sizeof(drreg_options_t), 3, false };
    drreg_status_t result = drreg_init(&ops);
    if ( result == DRREG_SUCCESS ) {
        dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE INIT 4] drreg_init is done.\n");
    } else {
        dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE INIT 4] drreg_init is NOT properly done.\n");
        DR_ASSERT(false);
    }

    if ( drwrap_init() ) {
        dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE INIT 5] drwrap_init is done.\n");
    } else {
        dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE INIT 5] drwrap_init is NOT properly done.\n");
        DR_ASSERT(false);
    }

    if ( drsym_init(0) == DRSYM_SUCCESS ) {
        dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE INIT 6] drsym_init is done.\n");
    } else {
        dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE INIT 6] drsym_init is NOT properly done.\n");
        DR_ASSERT(false);
    }

    client_id = id;
    mutex = dr_mutex_create();

    dr_register_exit_event(event_exit);
    drmgr_register_thread_init_event(event_thread_init);
    drmgr_register_thread_exit_event(event_thread_exit);
    drmgr_register_module_load_event(module_load_event);
    dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE INIT 7] module_load_event registration is done\n");

    drmgr_register_bb_instrumentation_event(event_bb_insert, NULL, NULL);
    dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 5, "[ARKADE INIT 8] BB(Basic Block) insertion is done\n\n");

    tls_idx = drmgr_register_tls_field();
    DR_ASSERT(tls_idx != -1);

    dr_log(NULL, DR_LOG_MASK_BASEOFFSET, 1, "Client 'memtrace' initializing\n");
}
