/*-
 * Copyright (c) 2011, 2012, 2013, Columbia University
 * All rights reserved.
 *
 * This software was developed by Vasileios P. Kemerlis <vpk@cs.columbia.edu>
 * at Columbia University, New York, NY, USA, in June 2011.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 *   * Redistributions of source code must retain the above copyright
 *     notice, this list of conditions and the following disclaimer.
 *   * Redistributions in binary form must reproduce the above copyright
 *     notice, this list of conditions and the following disclaimer in the
 *     documentation and/or other materials provided with the distribution.
 *   * Neither the name of Columbia University nor the
 *     names of its contributors may be used to endorse or promote products
 *     derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 */

#include <errno.h>
#include <string.h>
#include <wchar.h>
#include <set>
#include <assert.h>

#include "pin.H"
#include "libdft_api.h"
#include "libdft_analysis.h"
#include "libdft_instrument.h"
#include "tagmap.h"
#include "branch_pred.h"
extern "C" {
    #include "xed-interface.h"
}

int ins_count = 0;

/* set of unhandled instructions*/
 set<int> unhandled_ins_set;

/* thread context */
extern REG	thread_ctx_ptr;

/*
 * instruction inspection (instrumentation function)
 *
 * analyze every instruction and instrument it
 * for propagating the tag bits accordingly
 *
 * @ins:	the instruction to be instrumented
 */
void
#ifdef INS_INSTRUMENT
ins_inspect(INS ins, VOID *v)
#endif
#ifdef TRACE_INSTRUMENT
ins_inspect(INS ins)
#endif
{
    /*if(!instrumentFlag)
      return;
      */
    /* 
     * temporaries;
     * source, destination, base, and index registers
     */
    REG dst_reg, src_reg, reg_base, reg_indx, src1_reg, src2_reg;

    /* use XED to decode the instruction and extract its opcode */
    xed_iclass_enum_t ins_indx = (xed_iclass_enum_t)INS_Opcode(ins);

    /* sanity check */
    if (unlikely(ins_indx <= XED_ICLASS_INVALID || 
                ins_indx >= XED_ICLASS_LAST)) {
        LOG(string(__func__) + ": unknown opcode (opcode=" + 
                decstr(ins_indx) + ")\n");

        /* done */
        return;
    }
    //char *rtn_name_str = (char *)calloc(64, 1);
    string rtn_name_str = "";
#ifdef INS_DEBUG
    if(RTN_Valid(INS_Rtn(ins)))
        rtn_name_str = RTN_Name(INS_Rtn(ins));
    else
        rtn_name_str = "RTN Invalid";
    
    printLog("%s - %d: %s\n", 
            rtn_name_str.c_str(), ins_count++, 
            INS_Disassemble(ins).c_str());
#endif


    /* analyze the instruction */
    switch (ins_indx) {
        /* adc */
        case XED_ICLASS_ADC:
            /* add */
        case XED_ICLASS_ADD:
            /* and */
        case XED_ICLASS_AND:
            /* or */
        case XED_ICLASS_OR:
            /* xor */
        case XED_ICLASS_XOR:
            /* sbb */
        case XED_ICLASS_SBB:
            /* sub */
        case XED_ICLASS_SUB:
            //added ins:
        case XED_ICLASS_ADCX:
        case XED_ICLASS_ADOX:
        case XED_ICLASS_SUB_LOCK:
        case XED_ICLASS_OR_LOCK:
            /*
             * the general format of these instructions
             * is the following: dst {op}= src, where
             * op can be +, -, &, |, etc. We tag the
             * destination if the source is also taged
             * (i.e., t[dst] |= t[src])
             */
            /* 2nd operand is immediate; do nothing */
            if (INS_OperandIsImmediate(ins, OP_2))
                break;

            /* both operands are registers */
            if (INS_MemoryOperandCount(ins) == 0) 
            {
                /* extract the operands */
                dst_reg = INS_OperandReg(ins, OP_1);
                src_reg = INS_OperandReg(ins, OP_2);

                /* 64 or 32-bit reg operands */
                if (REG_is_gr64(dst_reg) || REG_is_gr32(dst_reg)) {
                    /* check for x86 clear register idiom */
                    switch (ins_indx) {
                        /* xor, sub, sbb */
                        case XED_ICLASS_XOR:
                        case XED_ICLASS_SUB:
                        case XED_ICLASS_SBB:
                            /* same dst, src */
                            if (dst_reg == src_reg) 
                            {
                                /* clear */
                                INS_InsertCall(ins,
                                        IPOINT_BEFORE,
                                        (AFUNPTR)r_clrl,
                                        IARG_FAST_ANALYSIS_CALL,
                                        IARG_REG_VALUE, 
                                        thread_ctx_ptr,
                                        IARG_UINT32, REG64_INDX(dst_reg),
                                        IARG_UINT32, ins_indx,
                                        //IARG_PTR, rtn_name_str,
                                        IARG_END);

                                /* done */
                                break;
                            }
                            /* default behavior */
                        default:
                            /* 
                             * propagate the tag
                             * markings accordingly
                             */
                            INS_InsertCall(ins,
                                    IPOINT_BEFORE,
                                    (AFUNPTR)r2r_binary_opl,
                                    IARG_FAST_ANALYSIS_CALL,
                                    IARG_REG_VALUE,
                                    thread_ctx_ptr,
                                    IARG_UINT32, REG64_INDX(dst_reg),
                                    IARG_UINT32, REG64_INDX(src_reg),
                                    IARG_UINT32, ins_indx,
                                    //IARG_PTR, rtn_name_str,
                                    IARG_END);
                    }
                }
                /* 16-bit operands */
                else if (REG_is_gr16(dst_reg)) {
                    /* check for x86 clear register idiom */
                    switch (ins_indx) {
                        /* xor, sub, sbb */
                        case XED_ICLASS_XOR:
                        case XED_ICLASS_SUB:
                        case XED_ICLASS_SBB:
                            /* same dst, src */
                            if (dst_reg == src_reg) 
                            {
                                /* clear */
                                INS_InsertCall(ins,
                                        IPOINT_BEFORE,
                                        (AFUNPTR)r_clrw,
                                        IARG_FAST_ANALYSIS_CALL,
                                        IARG_REG_VALUE, thread_ctx_ptr,
                                        IARG_UINT32, REG16_INDX(dst_reg),
                                        IARG_UINT32, ins_indx,
                                        //IARG_PTR, rtn_name_str,
                                        IARG_END);

                                /* done */
                                break;
                            }
                            /* default behavior */
                        default:
                            /* propagate tags accordingly */
                            INS_InsertCall(ins,
                                    IPOINT_BEFORE,
                                    (AFUNPTR)r2r_binary_opw,
                                    IARG_FAST_ANALYSIS_CALL,
                                    IARG_REG_VALUE, thread_ctx_ptr,
                                    IARG_UINT32, REG16_INDX(dst_reg),
                                    IARG_UINT32, REG16_INDX(src_reg),
                                    IARG_UINT32, ins_indx,
                                    //IARG_PTR, rtn_name_str,
                                    IARG_END);
                    }
                }
                /* 8-bit operands */
                else {
                    /* check for x86 clear register idiom */
                    switch (ins_indx) 
                    {
                        /* xor, sub, sbb */
                        case XED_ICLASS_XOR:
                        case XED_ICLASS_SUB:
                        case XED_ICLASS_SBB:
                            /* same dst, src */
                            if (dst_reg == src_reg) 
                            {
                                /* 8-bit upper */
                                if (REG_is_Upper8(dst_reg))
                                    /* clear */
                                    INS_InsertCall(ins,
                                            IPOINT_BEFORE,
                                            (AFUNPTR)r_clrb_u,
                                            IARG_FAST_ANALYSIS_CALL,
                                            IARG_REG_VALUE, thread_ctx_ptr,
                                            IARG_UINT32, REG8_INDX(dst_reg),
                                            IARG_UINT32, ins_indx,
                                            //IARG_PTR, rtn_name_str,
                                            IARG_END);
                                /* 8-bit lower */
                                else 
                                    /* clear */
                                    INS_InsertCall(ins,
                                            IPOINT_BEFORE,
                                            (AFUNPTR)r_clrb_l,
                                            IARG_FAST_ANALYSIS_CALL,
                                            IARG_REG_VALUE, thread_ctx_ptr,
                                            IARG_UINT32, REG8_INDX(dst_reg),
                                            IARG_UINT32, ins_indx,
                                            //IARG_PTR, rtn_name_str,
                                            IARG_END);

                                /* done */
                                break;
                            }
                            /* default behavior */
                        default:
                            /* propagate tags accordingly */
                            if (REG_is_Lower8(dst_reg) &&
                                    REG_is_Lower8(src_reg))
                                /* lower 8-bit registers */
                                INS_InsertCall(ins,
                                        IPOINT_BEFORE,
                                        (AFUNPTR)r2r_binary_opb_l,
                                        IARG_FAST_ANALYSIS_CALL,
                                        IARG_REG_VALUE, thread_ctx_ptr,
                                        IARG_UINT32, REG8_INDX(dst_reg),
                                        IARG_UINT32, REG8_INDX(src_reg),
                                        IARG_UINT32, ins_indx,
                                        //IARG_PTR, rtn_name_str,
                                        IARG_END);
                            else if(REG_is_Upper8(dst_reg) &&
                                    REG_is_Upper8(src_reg))
                                /* upper 8-bit registers */
                                INS_InsertCall(ins,
                                        IPOINT_BEFORE,
                                        (AFUNPTR)r2r_binary_opb_u,
                                        IARG_FAST_ANALYSIS_CALL,
                                        IARG_REG_VALUE, thread_ctx_ptr,
                                        IARG_UINT32, REG8_INDX(dst_reg),
                                        IARG_UINT32, REG8_INDX(src_reg),
                                        IARG_UINT32, ins_indx,
                                        //IARG_PTR, rtn_name_str,
                                        IARG_END);
                            else if (REG_is_Lower8(dst_reg))
                                /* 
                                 * destination register is a
                                 * lower 8-bit register and
                                 * source register is an upper
                                 * 8-bit register
                                 */
                                INS_InsertCall(ins,
                                        IPOINT_BEFORE,
                                        (AFUNPTR)r2r_binary_opb_lu,
                                        IARG_FAST_ANALYSIS_CALL,
                                        IARG_REG_VALUE, thread_ctx_ptr,
                                        IARG_UINT32, REG8_INDX(dst_reg),
                                        IARG_UINT32, REG8_INDX(src_reg),
                                        IARG_UINT32, ins_indx,
                                        //IARG_PTR, rtn_name_str,
                                        IARG_END);
                            else
                                /* 
                                 * destination register is an
                                 * upper 8-bit register and
                                 * source register is a lower
                                 * 8-bit register
                                 */
                                INS_InsertCall(ins,
                                        IPOINT_BEFORE,
                                        (AFUNPTR)r2r_binary_opb_ul,
                                        IARG_FAST_ANALYSIS_CALL,
                                        IARG_REG_VALUE, thread_ctx_ptr,
                                        IARG_UINT32, REG8_INDX(dst_reg),
                                        IARG_UINT32, REG8_INDX(src_reg),
                                        IARG_UINT32, ins_indx,
                                        //IARG_PTR, rtn_name_str,
                                        IARG_END);
                    }
                }
            }
            /* 
             * 2nd operand is memory;
             * we optimize for that case, since most
             * instructions will have a register as
             * the first operand -- leave the result
             * into the reg and use it later
             */
            else if (INS_OperandIsMemory(ins, OP_2)) 
            {
                /* extract the register operand */
                dst_reg = INS_OperandReg(ins, OP_1);

                /* 64-bit operands */
                if (REG_is_gr64(dst_reg))
                {
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)m2r_binary_opll,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG64_INDX(dst_reg),
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                }
                /* 32-bit operands */
                else if (REG_is_gr32(dst_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)m2r_binary_opl,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG64_INDX(dst_reg),
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 16-bit operands */
                else if (REG_is_gr16(dst_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)m2r_binary_opw,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG16_INDX(dst_reg),
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 8-bit operand (upper) */
                else if (REG_is_Upper8(dst_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)m2r_binary_opb_u,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG8_INDX(dst_reg),
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 8-bit operand (lower) */
                else 
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)m2r_binary_opb_l,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG8_INDX(dst_reg),
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
            }
            /* 1st operand is memory */
            else {
                /* extract the register operand */
                src_reg = INS_OperandReg(ins, OP_2);

                /* 64-bit operands */
                if (REG_is_gr64(src_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2m_binary_opll,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, REG64_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 32-bit operands */
                else if (REG_is_gr32(src_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2m_binary_opl,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, REG64_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 16-bit operands */
                else if (REG_is_gr16(src_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2m_binary_opw,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, REG16_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 8-bit operand (upper) */
                else if (REG_is_Upper8(src_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2m_binary_opb_u,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, REG8_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 8-bit operand (lower) */
                else
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2m_binary_opb_l,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, REG8_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
            }

            /* done */
            break;

            /*
             * Taint propagation form: dst = src1 | src2
             */
        case XED_ICLASS_ANDN:
        case XED_ICLASS_BEXTR:
        case XED_ICLASS_BZHI:
            dst_reg = INS_OperandReg(ins, OP_1);

            // all ops are regisers
            if(INS_MemoryOperandCount(ins) == 0)
                INS_InsertCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR)rr2r_binary_opl,
                        IARG_FAST_ANALYSIS_CALL,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, REG64_INDX(dst_reg),
                        IARG_UINT32, REG64_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT32, REG64_INDX(INS_OperandReg(ins, OP_3)),
                        IARG_UINT32, ins_indx,
                        //IARG_PTR, rtn_name_str,
                        IARG_END);
            // one memory op
            if(INS_MemoryOperandCount(ins) == 1) 
            {
                if(INS_OperandIsReg(ins, OP_2))
                {
                    // 64-bit
                    if(REG_is_gr64(dst_reg))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)rm2r_binary_opll,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT32, REG64_INDX(INS_OperandReg(ins, OP_2)),
                                IARG_MEMORYREAD_EA,
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    // src2 is 32-bit
                    else
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)rm2r_binary_opl,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT32, REG64_INDX(INS_OperandReg(ins, OP_2)),
                                IARG_MEMORYREAD_EA,
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                }
                // src1 is memory, src2 is reg
                else
                {
                    // 64-bit
                    if(REG_is_gr64(dst_reg))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)rm2r_binary_opll,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT32, REG64_INDX(INS_OperandReg(ins, OP_3)),
                                IARG_MEMORYREAD_EA,
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    // src2 is 32-bit
                    else
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)rm2r_binary_opl,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT32, REG64_INDX(INS_OperandReg(ins, OP_3)),
                                IARG_MEMORYREAD_EA,
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                }
            }

            /* done */
            break;

            /* bsf */
        case XED_ICLASS_BSF:
            /* bsr */
        case XED_ICLASS_BSR:
            /* mov */
        case XED_ICLASS_MOV:
            //added ins:
        case XED_ICLASS_BLSI:
        case XED_ICLASS_BLSMSK:
        case XED_ICLASS_BLSR:

        case XED_ICLASS_MOVBE:

            /*
             * the general format of these instructions
             * is the following: dst = src. We move the
             * tag of the source to the destination
             * (i.e., t[dst] = t[src])
             */
            /* 
             * 2nd operand is immediate or segment register;
             * clear the destination
             */
            if (INS_OperandIsImmediate(ins, OP_2) ||
                    (INS_OperandIsReg(ins, OP_2) &&
                     REG_is_seg(INS_OperandReg(ins, OP_2)))) 
            {
                /* destination operand is a memory address */
                if (INS_OperandIsMemory(ins, OP_1)) {
                    /* clear n-bytes */
                    switch (INS_OperandWidth(ins, OP_1)) {
                        /* 64_bits */
                        case MEM_LLONG_LEN:
                            /* propagate the tag accordingly */
                            INS_InsertCall(ins,
                                    IPOINT_BEFORE,
                                    (AFUNPTR)ins_clrll,
                                    IARG_FAST_ANALYSIS_CALL,
                                    IARG_MEMORYWRITE_EA,
                                    IARG_UINT32, ins_indx,
                                    //IARG_PTR, rtn_name_str,
                                    IARG_END);

                            /* done */
                            break;
                            /* 32_bits */
                        case MEM_LONG_LEN:
                            /* propagate the tag accordingly */
                            INS_InsertCall(ins,
                                    IPOINT_BEFORE,
                                    (AFUNPTR)ins_clrl,
                                    IARG_FAST_ANALYSIS_CALL,
                                    IARG_MEMORYWRITE_EA,
                                    IARG_UINT32, ins_indx,
                                    //IARG_PTR, rtn_name_str,
                                    IARG_END);

                            /* done */
                            break;
                            /* 2 bytes */
                        case MEM_WORD_LEN:
                            /* propagate the tag accordingly */
                            INS_InsertCall(ins,
                                    IPOINT_BEFORE,
                                    (AFUNPTR)ins_clrw,
                                    IARG_FAST_ANALYSIS_CALL,
                                    IARG_MEMORYWRITE_EA,
                                    IARG_UINT32, ins_indx,
                                    //IARG_PTR, rtn_name_str,
                                    IARG_END);

                            /* done */
                            break;
                            /* 1 byte */
                        case MEM_BYTE_LEN:
                            /* propagate the tag accordingly */
                            INS_InsertCall(ins,
                                    IPOINT_BEFORE,
                                    (AFUNPTR)ins_clrb,
                                    IARG_FAST_ANALYSIS_CALL,
                                    IARG_MEMORYWRITE_EA,
                                    IARG_UINT32, ins_indx,
                                    //IARG_PTR, rtn_name_str,
                                    IARG_END);

                            /* done */
                            break;
                            /* make the compiler happy */
                        default:
                            LOG(string(__func__) +
                                    ": unhandled operand width (" +
                                    INS_Disassemble(ins) + ")\n");

                            /* done */
                            return;
                    }
                }
                /* destination operand is a register */
                else if (INS_OperandIsReg(ins, OP_1)) {
                    /* extract the operand */
                    dst_reg = INS_OperandReg(ins, OP_1);

                    /* 64/32-bit operand */
                    if (REG_is_gr64(dst_reg) || REG_is_gr32(dst_reg))
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r_clrl,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    /* 16-bit operand */
                    else if (REG_is_gr16(dst_reg))
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r_clrw,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG16_INDX(dst_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    /* 8-bit operand (upper) */
                    else if (REG_is_Upper8(dst_reg))
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r_clrb_u,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    /* 8-bit operand (lower) */
                    else
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r_clrb_l,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                }
            }
            /* both operands are registers */
            else if (INS_MemoryOperandCount(ins) == 0) 
            {
                /* extract the operands */
                dst_reg = INS_OperandReg(ins, OP_1);
                src_reg = INS_OperandReg(ins, OP_2);

                /* 64/32-bit operands */
                if (REG_is_gr64(dst_reg) || REG_is_gr32(dst_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2r_xfer_opl,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG64_INDX(dst_reg),
                            IARG_UINT32, REG64_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 16-bit operands */
                else if (REG_is_gr16(dst_reg))
                    /* propagate tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2r_xfer_opw,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG16_INDX(dst_reg),
                            IARG_UINT32, REG16_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 8-bit operands */
                else if (REG_is_gr8(dst_reg)) {
                    /* propagate tag accordingly */
                    if (REG_is_Lower8(dst_reg) &&
                            REG_is_Lower8(src_reg))
                        /* lower 8-bit registers */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_xfer_opb_l,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    else if(REG_is_Upper8(dst_reg) &&
                            REG_is_Upper8(src_reg))
                        /* upper 8-bit registers */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_xfer_opb_u,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    else if (REG_is_Lower8(dst_reg))
                        /* 
                         * destination register is a
                         * lower 8-bit register and
                         * source register is an upper
                         * 8-bit register
                         */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_xfer_opb_lu,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    else
                        /* 
                         * destination register is an
                         * upper 8-bit register and
                         * source register is a lower
                         * 8-bit register
                         */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_xfer_opb_ul,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                }
            }
            /* 
             * 2nd operand is memory;
             * we optimize for that case, since most
             * instructions will have a register as
             * the first operand -- leave the result
             * into the reg and use it later
             */
            else if (INS_OperandIsMemory(ins, OP_2)) 
            {
                /* extract the register operand */
                dst_reg = INS_OperandReg(ins, OP_1);

                /* 64-bit operands */
                if (REG_is_gr64(dst_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)m2r_xfer_opll,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG64_INDX(dst_reg),
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 32-bit operands */
                else if (REG_is_gr32(dst_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)m2r_xfer_opl,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG64_INDX(dst_reg),
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 16-bit operands */
                else if (REG_is_gr16(dst_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)m2r_xfer_opw,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG16_INDX(dst_reg),
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 8-bit operands (upper) */
                else if (REG_is_Upper8(dst_reg)) 
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)m2r_xfer_opb_u,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG8_INDX(dst_reg),
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 8-bit operands (lower) */
                else
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)m2r_xfer_opb_l,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG8_INDX(dst_reg),
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
            }
            /* 1st operand is memory */
            else {
                /* extract the register operand */
                src_reg = INS_OperandReg(ins, OP_2);

                /* 64-bit operands */
                if (REG_is_gr64(src_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2m_xfer_opll,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, REG64_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 32-bit operands */
                else if (REG_is_gr32(src_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2m_xfer_opl,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, REG64_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 16-bit operands */
                else if (REG_is_gr16(src_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2m_xfer_opw,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, REG16_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 8-bit operands (upper) */
                else if (REG_is_Upper8(src_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2m_xfer_opb_u,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, REG8_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 8-bit operands (lower) */
                else 
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2m_xfer_opb_l,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, REG8_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
            }

            /* done */
            break;

            /* conditional movs */
        case XED_ICLASS_CMOVB:
        case XED_ICLASS_CMOVBE:
        case XED_ICLASS_CMOVL:
        case XED_ICLASS_CMOVLE:
        case XED_ICLASS_CMOVNB:
        case XED_ICLASS_CMOVNBE:
        case XED_ICLASS_CMOVNL:
        case XED_ICLASS_CMOVNLE:
        case XED_ICLASS_CMOVNO:
        case XED_ICLASS_CMOVNP:
        case XED_ICLASS_CMOVNS:
        case XED_ICLASS_CMOVNZ:
        case XED_ICLASS_CMOVO:
        case XED_ICLASS_CMOVP:
        case XED_ICLASS_CMOVS:
        case XED_ICLASS_CMOVZ:
            /*
             * the general format of these instructions
             * is the following: dst = src iff cond. We
             * move the tag of the source to the destination
             * iff the corresponding condition is met
             * (i.e., t[dst] = t[src])
             */
            /* both operands are registers */
            if (INS_MemoryOperandCount(ins) == 0) 
            {
                /* extract the operands */
                dst_reg = INS_OperandReg(ins, OP_1);
                src_reg = INS_OperandReg(ins, OP_2);

                /* 64/32-bit operands */
                if (REG_is_gr64(dst_reg) || REG_is_gr32(dst_reg))
                    /* propagate the tag accordingly */
                    INS_InsertPredicatedCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2r_xfer_opl,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG64_INDX(dst_reg),
                            IARG_UINT32, REG64_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 16-bit operands */
                else 
                    /* propagate tag accordingly */
                    INS_InsertPredicatedCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2r_xfer_opw,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG16_INDX(dst_reg),
                            IARG_UINT32, REG16_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
            }
            /* 
             * 2nd operand is memory;
             * we optimize for that case, since most
             * instructions will have a register as
             * the first operand -- leave the result
             * into the reg and use it later
             */
            else 
            {
                /* extract the register operand */
                dst_reg = INS_OperandReg(ins, OP_1);

                /* 64-bit operands */
                if (REG_is_gr64(dst_reg))
                    /* propagate the tag accordingly */
                    INS_InsertPredicatedCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)m2r_xfer_opll,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG64_INDX(dst_reg),
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 32-bit operands */
                else if (REG_is_gr32(dst_reg))
                    /* propagate the tag accordingly */
                    INS_InsertPredicatedCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)m2r_xfer_opl,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG64_INDX(dst_reg),
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 16-bit operands */
                else
                    /* propagate the tag accordingly */
                    INS_InsertPredicatedCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)m2r_xfer_opw,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG16_INDX(dst_reg),
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
            }

            /* done */
            break;
            /* 
             * cbw;
             * move the tag associated with AL to AX
             *
             * NOTE: sign extension generates data that
             * are dependent to the source operand
             */
        case XED_ICLASS_CBW:
            /* propagate the tag accordingly */
            INS_InsertCall(ins,
                    IPOINT_BEFORE,
                    (AFUNPTR)sx_r2r_opwb_l,
                    IARG_FAST_ANALYSIS_CALL,
                    IARG_REG_VALUE, thread_ctx_ptr,
                    IARG_UINT32, REG16_INDX(REG_AX),
                    IARG_UINT32, REG8_INDX(REG_AL),
                    IARG_UINT32, ins_indx,
                    //IARG_PTR, rtn_name_str,
                    IARG_END);

            /* done */
            break;
            /*
             * cwd;
             * move the tag associated with AX to EAX
             *
             * NOTE: sign extension generates data that
             * are dependent to the source operand
             */
        case XED_ICLASS_CWDE:
            /* propagate the tag accordingly */
            INS_InsertCall(ins,
                    IPOINT_BEFORE,
                    (AFUNPTR)sx_r2r_oplw,
                    IARG_FAST_ANALYSIS_CALL,
                    IARG_REG_VALUE, thread_ctx_ptr,
                    IARG_UINT32, REG64_INDX(REG_EAX),
                    IARG_UINT32, REG16_INDX(REG_AX),
                    IARG_UINT32, ins_indx,
                    //IARG_PTR, rtn_name_str,
                    IARG_END);

            /* done */
            break;
            /* 
             * cdqe;
             * move the tag associated with EAX to RAX
             *
             * NOTE: sign extension generates data that
             * are dependent to the source operand
             */
        case XED_ICLASS_CDQE:
            /* propagate the tag accordingly */
            INS_InsertCall(ins,
                    IPOINT_BEFORE,
                    (AFUNPTR)sx_r2r_oplll,
                    IARG_FAST_ANALYSIS_CALL,
                    IARG_REG_VALUE, thread_ctx_ptr,
                    IARG_UINT32, REG64_INDX(REG_RAX),
                    IARG_UINT32, REG64_INDX(REG_EAX),
                    IARG_UINT32, ins_indx,
                    //IARG_PTR, rtn_name_str,
                    IARG_END);

            /* done */
            break;

        case XED_ICLASS_CWD:
            INS_InsertCall(ins,
                    IPOINT_BEFORE,
                    (AFUNPTR)r2r_xfer_opw,
                    IARG_FAST_ANALYSIS_CALL,
                    IARG_REG_VALUE, thread_ctx_ptr,
                    IARG_UINT32, DX,
                    IARG_UINT32, AX,
                    IARG_UINT32, ins_indx,
                    //IARG_PTR, rtn_name_str,
                    IARG_END);

            /* done */
            break;

        case XED_ICLASS_CDQ:
            INS_InsertCall(ins,
                    IPOINT_BEFORE,
                    (AFUNPTR)r2r_xfer_opl,
                    IARG_FAST_ANALYSIS_CALL,
                    IARG_REG_VALUE, thread_ctx_ptr,
                    IARG_UINT32, RDX,
                    IARG_UINT32, RAX,
                    IARG_UINT32, ins_indx,
                    //IARG_PTR, rtn_name_str,
                    IARG_END);

            /* done */
            break;

        case XED_ICLASS_CQO:
            INS_InsertCall(ins,
                    IPOINT_BEFORE,
                    (AFUNPTR)r2r_xfer_opl,
                    IARG_FAST_ANALYSIS_CALL,
                    IARG_REG_VALUE, thread_ctx_ptr,
                    IARG_UINT32, RDX,
                    IARG_UINT32, RAX,
                    IARG_UINT32, ins_indx,
                    //IARG_PTR, rtn_name_str,
                    IARG_END);

            /* done */
            break;


            /* 
             * movsx;
             *
             * NOTE: sign extension generates data that
             * are dependent to the source operand
             */
        case XED_ICLASS_MOVSXD:
        case XED_ICLASS_MOVSX:
            /*
             * the general format of these instructions
             * is the following: dst = src. We move the
             * tag of the source to the destination
             * (i.e., t[dst] = t[src]) and we extend the
             * tag bits accordingly
             */
            /* both operands are registers */
            if (INS_MemoryOperandCount(ins) == 0) {
                /* extract the operands */
                dst_reg = INS_OperandReg(ins, OP_1);
                src_reg = INS_OperandReg(ins, OP_2);

                /*16-bit dst reg  */
                if (REG_is_gr16(dst_reg)) 
                {
                    /* upper 8-bit */
                    if (REG_is_Upper8(src_reg))
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)sx_r2r_opwb_u,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG16_INDX(dst_reg),
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    else
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)sx_r2r_opwb_l,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG16_INDX(dst_reg),
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                }
                // 32-bit dst reg
                else if (REG_is_gr32(dst_reg))
                {
                    /* 16-bit src operand */
                    if (REG_is_gr16(src_reg))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)sx_r2r_oplw,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT32, REG16_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    /* upper 8-bit src*/
                    else if (REG_is_Upper8(src_reg))
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)sx_r2r_oplb_u,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    /* lower 8-bit src */
                    else
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)sx_r2r_oplb_l,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                }
                // 64-bit dst reg
                else
                {
                    if(REG_is_gr32(src_reg))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)sx_r2r_oplll,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT32, REG64_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    else if(REG_is_gr16(src_reg))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)sx_r2r_opllw,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT32, REG16_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    /* upper 8-bit src*/
                    else if (REG_is_Upper8(src_reg))
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)sx_r2r_opllb_u,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    /* lower 8-bit src */
                    else
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)sx_r2r_opllb_l,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                }

            }
            /* 2nd operand is memory */
            else 
            {
                /* extract the operands */
                dst_reg = INS_OperandReg(ins, OP_1);

                /* 16-bit dst reg */
                if (REG_is_gr16(dst_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)sx_m2r_opwb,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG16_INDX(dst_reg),
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 32-bit dst reg */
                else if (REG_is_gr32(dst_reg))
                {
                    // 16 bit src operand
                    if (INS_MemoryOperandSize(ins, OP_1) ==
                            BIT2BYTE(MEM_WORD_LEN))
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)sx_m2r_oplw,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_MEMORYREAD_EA,
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    /* 8-bit src operands */
                    else
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)sx_m2r_oplb,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_MEMORYREAD_EA,
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                }
                // 64-bit dst reg
                else
                {
                    if(INS_MemoryOperandSize(ins, OP_1) == 
                            BIT2BYTE(MEM_LONG_LEN))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)sx_m2r_oplll,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_MEMORYREAD_EA,
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    // 16 bit src operand
                    if (INS_MemoryOperandSize(ins, OP_1) ==
                            BIT2BYTE(MEM_WORD_LEN))
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)sx_m2r_opllw,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_MEMORYREAD_EA,
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    /* 8-bit src operands */
                    else
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)sx_m2r_opllb,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_MEMORYREAD_EA,
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                }

            }

            /* done */
            break;

            /* 
             * movzx;
             *
             * NOTE: zero extension always results in
             * clearing the tags associated with the
             * higher bytes of the destination operand
             */
        case XED_ICLASS_MOVZX:
            /*
             * the general format of these instructions
             * is the following: dst = src. We move the
             * tag of the source to the destination
             * (i.e., t[dst] = t[src]) and we extend the
             * tag bits accordingly
             */
            /* both operands are registers */
            if (INS_MemoryOperandCount(ins) == 0) 
            {
                /* extract the operands */
                dst_reg = INS_OperandReg(ins, OP_1);
                src_reg = INS_OperandReg(ins, OP_2);

                /* 16-bit & 8-bit operands */
                if (REG_is_gr16(dst_reg)) {
                    /* upper 8-bit */
                    if (REG_is_Upper8(src_reg))
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)zx_r2r_opwb_u,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG16_INDX(dst_reg),
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    else
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)zx_r2r_opwb_l,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG16_INDX(dst_reg),
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                }
                /* 32-bit dst reg */
                else if(REG_is_gr32(dst_reg))
                {
                    if (REG_is_gr16(src_reg))
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)zx_r2r_oplw,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT32, REG16_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    /* 32-bit & 8-bit operands (upper 8-bit) */
                    else if (REG_is_Upper8(src_reg))
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)zx_r2r_oplb_u,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    /* 32-bit & 8-bit operands (lower 8-bit) */
                    else
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)zx_r2r_oplb_l,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                }
                // 64-bit dst reg
                else
                {
                    if (REG_is_gr16(src_reg))
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)zx_r2r_oplw,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT32, REG16_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    /* 32-bit & 8-bit operands (upper 8-bit) */
                    else if (REG_is_Upper8(src_reg))
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)zx_r2r_opllb_u,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    /* 32-bit & 8-bit operands (lower 8-bit) */
                    else
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)zx_r2r_opllb_l,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                }
            }
            /* 2nd operand is memory */
            else 
            {
                /* extract the operands */
                dst_reg = INS_OperandReg(ins, OP_1);

                /* 16-bit dst reg */
                if (REG_is_gr16(dst_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)zx_m2r_opwb,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG16_INDX(dst_reg),
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                // 32-bit dst reg
                else if (REG_is_gr32(dst_reg))
                {
                    /* 16-bit mem src */
                    if (INS_MemoryReadSize(ins) ==
                            BIT2BYTE(MEM_WORD_LEN))
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)zx_m2r_oplw,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_MEMORYREAD_EA,
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    /* 8-bit mem src */
                    else
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)zx_m2r_oplb,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_MEMORYREAD_EA,
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                }
                // 64-bit dst reg
                else
                {
                    /* 16-bit mem src */
                    if (INS_MemoryReadSize(ins) ==
                            BIT2BYTE(MEM_WORD_LEN))
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)zx_m2r_opllw,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_MEMORYREAD_EA,
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    /* 8-bit mem src */
                    else
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)zx_m2r_opllb,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_MEMORYREAD_EA,
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                }
            }

            /* done */
            break;
            /* div */
        case XED_ICLASS_DIV:
            /* idiv */
        case XED_ICLASS_IDIV:
            /*
             * the general format of these brain-dead and
             * totally corrupted instructions is the following:
             * dst1:dst2 {*, /}= src. We tag the destination
             * operands if the source is also taged
             * (i.e., t[dst1]:t[dst2] |= t[src])
             */
            /* memory operand */
            if (INS_OperandIsMemory(ins, OP_1))
                /* differentiate based on the memory size */
                switch (INS_MemoryReadSize(ins)) {
                    /* 8 bytes */
                    case BIT2BYTE(MEM_LLONG_LEN):
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)m2r_div_opll,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                        break;
                        /* 4 bytes */
                    case BIT2BYTE(MEM_LONG_LEN):
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)m2r_div_opl,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);

                        /* done */
                        break;
                        /* 2 bytes */
                    case BIT2BYTE(MEM_WORD_LEN):
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)m2r_div_opw,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);

                        /* done */
                        break;
                        /* 1 byte */
                    case BIT2BYTE(MEM_BYTE_LEN):
                    default:
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)m2r_div_opb,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);

                        /* done */
                        break;
                }
            /* register operand */
            else {
                /* extract the operand */
                src_reg = INS_OperandReg(ins, OP_1);

                /* 32/64-bit operand */
                if (REG_is_gr64(src_reg) || REG_is_gr32(src_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2r_div_opl,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG64_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 16-bit operand */
                else if (REG_is_gr16(src_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2r_div_opw,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG16_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 8-bit operand (upper) */
                else if (REG_is_Upper8(src_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2r_div_opb_u,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG8_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 8-bit operand (lower) */
                else 
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2r_div_opl,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG8_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
            }

            /* done */
            break;

            /*
             * imul;
             * I'm still wondering how brain-damaged the
             * ISA architect should be in order to come
             * up with something so ugly as the IMUL 
             * instruction
             */
        case XED_ICLASS_MUL:
        case XED_ICLASS_IMUL:
            /* one-operand form */
            if (INS_OperandIsImplicit(ins, OP_2)) {
                /* memory operand */
                if (INS_OperandIsMemory(ins, OP_1))
                    /* differentiate based on the memory size */
                    switch (INS_MemoryWriteSize(ins)) {
                        /* 8 bytes */
                        case BIT2BYTE(MEM_LLONG_LEN):
                            /* propagate the tag accordingly */
                            INS_InsertCall(ins,
                                    IPOINT_BEFORE,
                                    (AFUNPTR)m2r_mul_opll,
                                    IARG_FAST_ANALYSIS_CALL,
                                    IARG_REG_VALUE, thread_ctx_ptr,
                                    IARG_MEMORYREAD_EA,
                                    IARG_UINT32, ins_indx,
                                    //IARG_PTR, rtn_name_str,
                                    IARG_END);

                            /* done */
                            break;
                            /* 4 bytes */
                        case BIT2BYTE(MEM_LONG_LEN):
                            /* propagate the tag accordingly */
                            INS_InsertCall(ins,
                                    IPOINT_BEFORE,
                                    (AFUNPTR)m2r_mul_opl,
                                    IARG_FAST_ANALYSIS_CALL,
                                    IARG_REG_VALUE, thread_ctx_ptr,
                                    IARG_MEMORYREAD_EA,
                                    IARG_UINT32, ins_indx,
                                    //IARG_PTR, rtn_name_str,
                                    IARG_END);

                            /* done */
                            break;
                            /* 2 bytes */
                        case BIT2BYTE(MEM_WORD_LEN):
                            /* propagate the tag accordingly */
                            INS_InsertCall(ins,
                                    IPOINT_BEFORE,
                                    (AFUNPTR)m2r_mul_opw,
                                    IARG_FAST_ANALYSIS_CALL,
                                    IARG_REG_VALUE, thread_ctx_ptr,
                                    IARG_MEMORYREAD_EA,
                                    IARG_UINT32, ins_indx,
                                    //IARG_PTR, rtn_name_str,
                                    IARG_END);

                            /* done */
                            break;
                            /* 1 byte */
                        case BIT2BYTE(MEM_BYTE_LEN):
                        default:
                            /* propagate the tag accordingly */
                            INS_InsertCall(ins,
                                    IPOINT_BEFORE,
                                    (AFUNPTR)m2r_mul_opb,
                                    IARG_FAST_ANALYSIS_CALL,
                                    IARG_REG_VALUE, thread_ctx_ptr,
                                    IARG_MEMORYREAD_EA,
                                    IARG_UINT32, ins_indx,
                                    //IARG_PTR, rtn_name_str,
                                    IARG_END);

                            /* done */
                            break;
                    }

                /* register operand */
                else {
                    /* extract the operand */
                    src_reg = INS_OperandReg(ins, OP_1);

                    /* 32/64-bit operand */
                    if (REG_is_gr64(src_reg) || REG_is_gr32(src_reg))
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_mul_opl,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    /* 16-bit operand */
                    else if (REG_is_gr16(src_reg))
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_mul_opw,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG16_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    /* 8-bit operand (upper) */
                    else if (REG_is_Upper8(src_reg))
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_mul_opb_u,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    /* 8-bit operand (lower) */
                    else
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_mul_opb_l,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                }
            }

            /* two/three-operands form */
            else {
                /* 2nd operand is immediate; do nothing */
                if (INS_OperandIsImmediate(ins, OP_2))
                    break;

                /* both operands are registers */
                if (INS_MemoryOperandCount(ins) == 0) {
                    /* extract the operands */
                    dst_reg = INS_OperandReg(ins, OP_1);
                    src_reg = INS_OperandReg(ins, OP_2);

                    /* 32/64-bit operands */
                    if (REG_is_gr64(dst_reg) || REG_is_gr32(dst_reg))
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_binary_opl,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT32, REG64_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    /* 16-bit operands */
                    else
                        /* propagate tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_binary_opw,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG16_INDX(dst_reg),
                                IARG_UINT32, REG16_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                }
                /* 
                 * 2nd operand is memory;
                 * we optimize for that case, since most
                 * instructions will have a register as
                 * the first operand -- leave the result
                 * into the reg and use it later
                 */
                else {
                    /* extract the register operand */
                    dst_reg = INS_OperandReg(ins, OP_1);

                    /* 64-bit operands */
                    if (REG_is_gr64(dst_reg))
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)m2r_binary_opll,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_MEMORYREAD_EA,
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    /* 32-bit operands */
                    else if (REG_is_gr32(dst_reg))
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)m2r_binary_opl,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_MEMORYREAD_EA,
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    /* 16-bit operands */
                    else
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)m2r_binary_opw,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG16_INDX(dst_reg),
                                IARG_MEMORYREAD_EA,
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                }
            }

            /* done */
            break;
            /* conditional sets */
        case XED_ICLASS_SETB:
        case XED_ICLASS_SETBE:
        case XED_ICLASS_SETL:
        case XED_ICLASS_SETLE:
        case XED_ICLASS_SETNB:
        case XED_ICLASS_SETNBE:
        case XED_ICLASS_SETNL:
        case XED_ICLASS_SETNLE:
        case XED_ICLASS_SETNO:
        case XED_ICLASS_SETNP:
        case XED_ICLASS_SETNS:
        case XED_ICLASS_SETNZ:
        case XED_ICLASS_SETO:
        case XED_ICLASS_SETP:
        case XED_ICLASS_SETS:
        case XED_ICLASS_SETZ:
            /*
             * clear the tag information associated with the
             * destination operand
             */
            /* register operand */
            if (INS_MemoryOperandCount(ins) == 0) {
                /* extract the operand */
                dst_reg = INS_OperandReg(ins, OP_1);

                /* 8-bit operand (upper) */
                if (REG_is_Upper8(dst_reg))	
                    /* propagate tag accordingly */
                    INS_InsertPredicatedCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r_clrb_u,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG8_INDX(dst_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 8-bit operand (lower) */
                else 
                    /* propagate tag accordingly */
                    INS_InsertPredicatedCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r_clrb_l,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG8_INDX(dst_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
            }
            /* memory operand */
            else
                /* propagate the tag accordingly */
                INS_InsertPredicatedCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR)ins_clrb,
                        IARG_FAST_ANALYSIS_CALL,
                        IARG_MEMORYWRITE_EA,
                        IARG_UINT32, ins_indx,
                        //IARG_PTR, rtn_name_str,
                        IARG_END);

            /* done */
            break;
            /* 
             * stmxcsr;
             * clear the destination operand (memory location)
             */
        case XED_ICLASS_STMXCSR:
            /* propagate tag accordingly */
            INS_InsertCall(ins,
                    IPOINT_BEFORE,
                    (AFUNPTR)ins_clrl,
                    IARG_FAST_ANALYSIS_CALL,
                    IARG_MEMORYWRITE_EA,
                    IARG_UINT32, ins_indx,
                    //IARG_PTR, rtn_name_str,
                    IARG_END);

            /* done */
            break;
            /* 
             * smsw;
             *
             * NOTE: When the processor moves the CR0 control
             * register into a 32-bit general-purpose register,
             * it assumes that the 16 least-significant bits of
             * the general-purpose register are the destination
             * or source operand. If the register is a destination
             * operand, the resulting value in the two high-order
             * bytes of the register is undefined.
             */
        case XED_ICLASS_SMSW:
            /* str */
        case XED_ICLASS_STR:
            /*
             * clear the tag information associated with
             * the destination operand
             */
            /* register operand */
            if (INS_MemoryOperandCount(ins) == 0) {
                /* extract the operand */
                dst_reg = INS_OperandReg(ins, OP_1);

                /* 16-bit register */
                if (REG_is_gr16(dst_reg))
                    /* propagate tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r_clrw,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG16_INDX(dst_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 32/64-bit register */
                else 
                    /* propagate tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r_clrl,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG64_INDX(dst_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
            }
            /* memory operand */
            else
                /* propagate tag accordingly */
                INS_InsertCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR)ins_clrw,
                        IARG_FAST_ANALYSIS_CALL,
                        IARG_MEMORYWRITE_EA,
                        IARG_UINT32, ins_indx,
                        //IARG_PTR, rtn_name_str,
                        IARG_END);

            /* done */
            break;
            /* 
             * lar;
             * clear the destination operand (register only)
             */
        case XED_ICLASS_LAR:
            /* extract the 1st operand */
            dst_reg = INS_OperandReg(ins, OP_1);

            /* 16-bit register */
            if (REG_is_gr16(dst_reg))
                /* propagate tag accordingly */
                INS_InsertCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR)r_clrw,
                        IARG_FAST_ANALYSIS_CALL,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, REG16_INDX(dst_reg),
                        IARG_UINT32, ins_indx,
                        //IARG_PTR, rtn_name_str,
                        IARG_END);
            /* 32-bit register */
            else
                /* propagate tag accordingly */
                INS_InsertCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR)r_clrl,
                        IARG_FAST_ANALYSIS_CALL,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, REG64_INDX(dst_reg),
                        IARG_UINT32, ins_indx,
                        //IARG_PTR, rtn_name_str,
                        IARG_END);

            /* done */
            break;
            /* rdpmc */
        case XED_ICLASS_RDPMC:
            /* rdtsc */
        case XED_ICLASS_RDTSC:
            /*
             * clear the tag information associated with
             * EAX and EDX
             */
            /* propagate tag accordingly */
            INS_InsertCall(ins,
                    IPOINT_BEFORE,
                    (AFUNPTR)r_clrl2,
                    IARG_FAST_ANALYSIS_CALL,
                    IARG_REG_VALUE, thread_ctx_ptr,
                    IARG_UINT32, ins_indx,
                    //IARG_PTR, rtn_name_str,
                    IARG_END);

            /* done */
            break;
            /* 
             * cpuid;
             * clear the tag information associated with
             * EAX, EBX, ECX, and EDX 
             */
        case XED_ICLASS_CPUID:
            /* propagate tag accordingly */
            INS_InsertCall(ins,
                    IPOINT_BEFORE,
                    (AFUNPTR)r_clrl4,
                    IARG_FAST_ANALYSIS_CALL,
                    IARG_REG_VALUE, thread_ctx_ptr,
                    IARG_UINT32, ins_indx,
                    //IARG_PTR, rtn_name_str,
                    IARG_END);

            /* done */
            break;
            /* 
             * lahf;
             * clear the tag information of AH
             */
        case XED_ICLASS_LAHF:
            /* propagate tag accordingly */
            INS_InsertCall(ins,
                    IPOINT_BEFORE,
                    (AFUNPTR)r_clrb_u,
                    IARG_FAST_ANALYSIS_CALL,
                    IARG_REG_VALUE, thread_ctx_ptr,
                    IARG_UINT32, REG8_INDX(REG_AH),
                    IARG_UINT32, ins_indx,
                    //IARG_PTR, rtn_name_str,
                    IARG_END);

            /* done */
            break;
            /* 
             * cmpxchg;
             * t[dst] = t[src] iff EAX/AX/AL == dst, else
             * t[EAX/AX/AL] = t[dst] -- yes late-night coding again
             * and I'm really tired to comment this crap...
             */
        case XED_ICLASS_CMPXCHG:
        case XED_ICLASS_CMPXCHG_LOCK:
            /* both operands are registers */
            if (INS_MemoryOperandCount(ins) == 0) {
                /* extract the operands */
                dst_reg = INS_OperandReg(ins, OP_1);
                src_reg = INS_OperandReg(ins, OP_2);

                if (REG_is_gr64(dst_reg) || REG_is_gr32(dst_reg)) {
                    /* propagate tag accordingly; fast path */
                    INS_InsertIfCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)_cmpxchg_r2r_opl_fast,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_REG_VALUE, REG_EAX,
                            IARG_UINT32, REG64_INDX(dst_reg),
                            IARG_REG_VALUE, dst_reg,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                    /* propagate tag accordingly; slow path */
                    INS_InsertThenCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)_cmpxchg_r2r_opl_slow,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG64_INDX(dst_reg),
                            IARG_UINT32, REG64_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                }
                /* 16-bit operands */
                else if (REG_is_gr16(dst_reg)) {
                    /* propagate tag accordingly; fast path */
                    INS_InsertIfCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)_cmpxchg_r2r_opw_fast,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_REG_VALUE, REG_AX,
                            IARG_UINT32, REG16_INDX(dst_reg),
                            IARG_REG_VALUE, dst_reg,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                    /* propagate tag accordingly; slow path */
                    INS_InsertThenCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)_cmpxchg_r2r_opw_slow,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG16_INDX(dst_reg),
                            IARG_UINT32, REG16_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                }
                /* 8-bit operands */
                else
                    printLog("unhandled opcode %s\n", 
                            OPCODE_StringShort(ins_indx));
            }
            /* 1st operand is memory */
            else {
                /* extract the operand */
                src_reg = INS_OperandReg(ins, OP_2);

                /* 64-bit operands */
                if (REG_is_gr64(src_reg)) {
                    /* propagate tag accordingly; fast path */
                    INS_InsertIfCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)_cmpxchg_m2r_opll_fast,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_REG_VALUE, REG_RAX,
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                    /* propagate tag accordingly; slow path */
                    INS_InsertThenCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)_cmpxchg_r2m_opll_slow,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, REG64_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                }
                /* 32-bit operands */
                else if (REG_is_gr32(src_reg)) {
                    /* propagate tag accordingly; fast path */
                    INS_InsertIfCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)_cmpxchg_m2r_opl_fast,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_REG_VALUE, REG_EAX,
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                    /* propagate tag accordingly; slow path */
                    INS_InsertThenCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)_cmpxchg_r2m_opl_slow,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, REG64_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                }
                /* 16-bit operands */
                else if (REG_is_gr16(src_reg)) {
                    /* propagate tag accordingly; fast path */
                    INS_InsertIfCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)_cmpxchg_m2r_opw_fast,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_REG_VALUE, REG_AX,
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                    /* propagate tag accordingly; slow path */
                    INS_InsertThenCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)_cmpxchg_r2m_opw_slow,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, REG16_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                }
                /* 8-bit operands */
                else
                    printLog("unhandled opcode: %s\n", 
                            OPCODE_StringShort(ins_indx));
            }

            /* done */
            break;

        case XED_ICLASS_CMPXCHG16B:
        case XED_ICLASS_CMPXCHG16B_LOCK:
            /* propagate tag accordingly; fast path */
            INS_InsertIfCall(ins,
                    IPOINT_BEFORE,
                    (AFUNPTR)cmpxchg16_r2m_neq,
                    IARG_FAST_ANALYSIS_CALL,
                    IARG_REG_VALUE, thread_ctx_ptr,
                    IARG_REG_VALUE, REG_GDX,
                    IARG_REG_VALUE, REG_GAX,
                    IARG_MEMORYREAD_EA,
                    IARG_UINT32, ins_indx,
                    //IARG_PTR, rtn_name_str,
                    IARG_END);
            /* propagate tag accordingly; slow path */
            INS_InsertThenCall(ins,
                    IPOINT_BEFORE,
                    (AFUNPTR)cmpxchg16_r2m_eq,
                    IARG_FAST_ANALYSIS_CALL,
                    IARG_REG_VALUE, thread_ctx_ptr,
                    IARG_REG_VALUE, REG_GCX,
                    IARG_REG_VALUE, REG_GBX,
                    IARG_MEMORYREAD_EA,
                    IARG_UINT32, ins_indx,
                    //IARG_PTR, rtn_name_str,
                    IARG_END);

            // done
            break;

        case XED_ICLASS_CMPXCHG8B:
        case XED_ICLASS_CMPXCHG8B_LOCK:
            /* propagate tag accordingly; fast path */
            INS_InsertIfCall(ins,
                    IPOINT_BEFORE,
                    (AFUNPTR)cmpxchg8_r2m_neq,
                    IARG_FAST_ANALYSIS_CALL,
                    IARG_REG_VALUE, thread_ctx_ptr,
                    IARG_REG_VALUE, REG_EDX,
                    IARG_REG_VALUE, REG_EAX,
                    IARG_MEMORYREAD_EA,
                    IARG_UINT32, ins_indx,
                    //IARG_PTR, rtn_name_str,
                    IARG_END);
            /* propagate tag accordingly; slow path */
            INS_InsertThenCall(ins,
                    IPOINT_BEFORE,
                    (AFUNPTR)cmpxchg8_r2m_eq,
                    IARG_FAST_ANALYSIS_CALL,
                    IARG_REG_VALUE, thread_ctx_ptr,
                    IARG_REG_VALUE, REG_ECX,
                    IARG_REG_VALUE, REG_EBX,
                    IARG_MEMORYREAD_EA,
                    IARG_UINT32, ins_indx,
                    //IARG_PTR, rtn_name_str,
                    IARG_END);

            // done
            break;

            /* 
             * xchg;
             * exchange the tag information of the two operands
             */
        case XED_ICLASS_XCHG:
            /* both operands are registers */
            if (INS_MemoryOperandCount(ins) == 0) {
                /* extract the operands */
                dst_reg = INS_OperandReg(ins, OP_1);
                src_reg = INS_OperandReg(ins, OP_2);

                /* 32/64-bit operands */
                if (REG_is_gr64(dst_reg) || REG_is_gr32(dst_reg)) {
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2r_xfer_opl,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, GPR_SCRATCH,
                            IARG_UINT32, REG64_INDX(dst_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2r_xfer_opl,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG64_INDX(dst_reg),
                            IARG_UINT32, REG64_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2r_xfer_opl,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG64_INDX(src_reg),
                            IARG_UINT32, GPR_SCRATCH,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                }
                /* 16-bit operands */
                else if (REG_is_gr16(dst_reg)) { 
                    /* propagate tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2r_xfer_opw,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, GPR_SCRATCH,
                            IARG_UINT32, REG16_INDX(dst_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2r_xfer_opw,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG16_INDX(dst_reg),
                            IARG_UINT32, REG16_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2r_xfer_opw,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG16_INDX(src_reg),
                            IARG_UINT32, GPR_SCRATCH,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                }
                /* 8-bit operands */
                else if (REG_is_gr8(dst_reg)) {
                    /* propagate tag accordingly */
                    if (REG_is_Lower8(dst_reg) &&
                            REG_is_Lower8(src_reg)) {
                        /* lower 8-bit registers */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_xfer_opb_l,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, GPR_SCRATCH,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_xfer_opb_l,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_xfer_opb_l,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, GPR_SCRATCH,
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    }
                    else if(REG_is_Upper8(dst_reg) &&
                            REG_is_Upper8(src_reg)) {
                        /* upper 8-bit registers */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_xfer_opb_u,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, GPR_SCRATCH,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_xfer_opb_u,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_xfer_opb_u,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, GPR_SCRATCH,
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    }
                    else if (REG_is_Lower8(dst_reg)) {
                        /* 
                         * destination register is a
                         * lower 8-bit register and
                         * source register is an upper
                         * 8-bit register
                         */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_xfer_opb_l,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, GPR_SCRATCH,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_xfer_opb_lu,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_xfer_opb_ul,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, GPR_SCRATCH,
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    }
                    else {
                        /* 
                         * destination register is an
                         * upper 8-bit register and
                         * source register is a lower
                         * 8-bit register
                         */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_xfer_opb_u,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, GPR_SCRATCH,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_xfer_opb_ul,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_xfer_opb_lu,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, GPR_SCRATCH,
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    }
                }
            }
            /* 
             * 2nd operand is memory;
             * we optimize for that case, since most
             * instructions will have a register as
             * the first operand -- leave the result
             * into the reg and use it later
             */
            else if (INS_OperandIsMemory(ins, OP_2)) {
                /* extract the register operand */
                dst_reg = INS_OperandReg(ins, OP_1);

                /* 64-bit operands */
                if (REG_is_gr64(dst_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)_xchg_r2m_opll,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, REG64_INDX(dst_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 32-bit operands */
                else if (REG_is_gr32(dst_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)_xchg_r2m_opl,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, REG64_INDX(dst_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 16-bit operands */
                else if (REG_is_gr16(dst_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)_xchg_r2m_opw,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, REG16_INDX(dst_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 8-bit operands (upper) */
                else if (REG_is_Upper8(dst_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)_xchg_r2m_opb_u,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, REG8_INDX(dst_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 8-bit operands (lower) */
                else
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)_xchg_r2m_opb_l,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, REG8_INDX(dst_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
            }
            /* 1st operand is memory */
            else {
                /* extract the register operand */
                src_reg = INS_OperandReg(ins, OP_2);

                /* 64-bit operands */
                if (REG_is_gr64(src_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)_xchg_r2m_opll,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, REG64_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 32-bit operands */
                else if (REG_is_gr32(src_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)_xchg_r2m_opl,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, REG64_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 16-bit operands */
                else if (REG_is_gr16(src_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)_xchg_r2m_opw,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, REG16_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 8-bit operands (upper) */
                else if (REG_is_Upper8(src_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)_xchg_r2m_opb_u,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, REG8_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 8-bit operands (lower) */
                else
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)_xchg_r2m_opb_l,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, REG8_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
            }

            /* done */
            break;
            /* 
             * xadd;
             * xchg + add. We instrument this instruction  using the tag
             * logic of xchg and add (see above)
             */
        case XED_ICLASS_XADD:
        case XED_ICLASS_XADD_LOCK:
            /* both operands are registers */
            if (INS_MemoryOperandCount(ins) == 0) {
                /* extract the operands */
                dst_reg = INS_OperandReg(ins, OP_1);
                src_reg = INS_OperandReg(ins, OP_2);

                /* 32/64-bit operands */
                if (REG_is_gr64(dst_reg) || REG_is_gr32(dst_reg)) {
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2r_xfer_opl,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, GPR_SCRATCH,
                            IARG_UINT32, REG64_INDX(dst_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2r_xfer_opl,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG64_INDX(dst_reg),
                            IARG_UINT32, REG64_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2r_xfer_opl,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG64_INDX(src_reg),
                            IARG_UINT32, GPR_SCRATCH,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2r_binary_opl,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG64_INDX(dst_reg),
                            IARG_UINT32, REG64_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                }
                /* 16-bit operands */
                else if (REG_is_gr16(dst_reg)) { 
                    /* propagate tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2r_xfer_opw,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, GPR_SCRATCH,
                            IARG_UINT32, REG16_INDX(dst_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2r_xfer_opw,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG16_INDX(dst_reg),
                            IARG_UINT32, REG16_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2r_xfer_opw,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG16_INDX(src_reg),
                            IARG_UINT32, GPR_SCRATCH,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2r_binary_opw,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG16_INDX(dst_reg),
                            IARG_UINT32, REG16_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                }
                /* 8-bit operands */
                else if (REG_is_gr8(dst_reg)) {
                    /* propagate tag accordingly */
                    if (REG_is_Lower8(dst_reg) &&
                            REG_is_Lower8(src_reg)) {
                        /* lower 8-bit registers */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_xfer_opb_l,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, GPR_SCRATCH,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_xfer_opb_l,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_xfer_opb_l,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, GPR_SCRATCH,
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_binary_opb_l,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    }
                    else if(REG_is_Upper8(dst_reg) &&
                            REG_is_Upper8(src_reg)) {
                        /* upper 8-bit registers */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_xfer_opb_u,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, GPR_SCRATCH,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_xfer_opb_u,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_xfer_opb_u,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, GPR_SCRATCH,
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_binary_opb_u,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    }
                    else if (REG_is_Lower8(dst_reg)) {
                        /* 
                         * destination register is a
                         * lower 8-bit register and
                         * source register is an upper
                         * 8-bit register
                         */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_xfer_opb_l,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, GPR_SCRATCH,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_xfer_opb_lu,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_xfer_opb_ul,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, GPR_SCRATCH,
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_binary_opb_lu,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    }
                    else {
                        /* 
                         * destination register is an
                         * upper 8-bit register and
                         * source register is a lower
                         * 8-bit register
                         */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_xfer_opb_u,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, GPR_SCRATCH,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_xfer_opb_ul,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_xfer_opb_lu,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, GPR_SCRATCH,
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)r2r_binary_opb_ul,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_UINT32, REG8_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                    }
                }
            }
            /* 1st operand is memory */
            else {
                /* extract the register operand */
                src_reg = INS_OperandReg(ins, OP_2);

                /* 64-bit operands */
                if (REG_is_gr64(src_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)_xadd_r2m_opll,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, REG64_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 32-bit operands */
                else if (REG_is_gr32(src_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)_xadd_r2m_opl,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, REG64_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 16-bit operands */
                else if (REG_is_gr16(src_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)_xadd_r2m_opw,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, REG16_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 8-bit operand (upper) */
                else if (REG_is_Upper8(src_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)_xadd_r2m_opb_u,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, REG8_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 8-bit operand (lower) */
                else
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)_xadd_r2m_opb_l,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, REG8_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
            }

            /* done */
            break;
            /* xlat; similar to a mov between a memory location and AL */
        case XED_ICLASS_XLAT:
            /* propagate the tag accordingly */
            INS_InsertCall(ins,
                    IPOINT_BEFORE,
                    (AFUNPTR)m2r_xfer_opb_l,
                    IARG_FAST_ANALYSIS_CALL,
                    IARG_REG_VALUE, thread_ctx_ptr,
                    IARG_UINT32, REG8_INDX(REG_AL),
                    IARG_MEMORYREAD_EA,
                    IARG_UINT32, ins_indx,
                    //IARG_PTR, rtn_name_str,
                    IARG_END);

            /* done */
            break;
            /* lodsb; similar to a mov between a memory location and AL */
        case XED_ICLASS_LODSB:
            /* propagate the tag accordingly */
            INS_InsertPredicatedCall(ins,
                    IPOINT_BEFORE,
                    (AFUNPTR)m2r_xfer_opb_l,
                    IARG_FAST_ANALYSIS_CALL,
                    IARG_REG_VALUE, thread_ctx_ptr,
                    IARG_UINT32, REG8_INDX(REG_AL),
                    IARG_MEMORYREAD_EA,
                    IARG_UINT32, ins_indx,
                    //IARG_PTR, rtn_name_str,
                    IARG_END);

            /* done */
            break;
            /* lodsw; similar to a mov between a memory location and AX */
        case XED_ICLASS_LODSW:
            /* propagate the tag accordingly */
            INS_InsertPredicatedCall(ins,
                    IPOINT_BEFORE,
                    (AFUNPTR)m2r_xfer_opw,
                    IARG_FAST_ANALYSIS_CALL,
                    IARG_REG_VALUE, thread_ctx_ptr,
                    IARG_UINT32, REG16_INDX(REG_AX),
                    IARG_MEMORYREAD_EA,
                    IARG_UINT32, ins_indx,
                    //IARG_PTR, rtn_name_str,
                    IARG_END);

            /* done */
            break;
            /* lodsd; similar to a mov between a memory location and EAX */
        case XED_ICLASS_LODSD:
            /* propagate the tag accordingly */
            INS_InsertPredicatedCall(ins,
                    IPOINT_BEFORE,
                    (AFUNPTR)m2r_xfer_opl,
                    IARG_FAST_ANALYSIS_CALL,
                    IARG_REG_VALUE, thread_ctx_ptr,
                    IARG_UINT32, REG64_INDX(REG_EAX),
                    IARG_MEMORYREAD_EA,
                    IARG_UINT32, ins_indx,
                    //IARG_PTR, rtn_name_str,
                    IARG_END);

            /* done */
            break;
            /* lodsq; similar to a mov between a memory location and RAX */
        case XED_ICLASS_LODSQ:
            /* propagate the tag accordingly */
            INS_InsertPredicatedCall(ins,
                    IPOINT_BEFORE,
                    (AFUNPTR)m2r_xfer_opll,
                    IARG_FAST_ANALYSIS_CALL,
                    IARG_REG_VALUE, thread_ctx_ptr,
                    IARG_UINT32, REG64_INDX(REG_GAX),
                    IARG_MEMORYREAD_EA,
                    IARG_UINT32, ins_indx,
                    //IARG_PTR, rtn_name_str,
                    IARG_END);

            /* done */
            break;
            /* 
             * stosb;
             * the opposite of lodsb; however, since the instruction can
             * also be prefixed with 'rep', the analysis code moves the
             * tag information, accordingly, only once (i.e., before the
             * first repetition) -- typically this will not lead in
             * inlined code
             */
        case XED_ICLASS_STOSB:
#if 0 
            /* the instruction is rep prefixed */
            if (INS_RepPrefix(ins)) {
                /* propagate the tag accordingly */
                INS_InsertIfPredicatedCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR)rep_predicate,
                        IARG_FAST_ANALYSIS_CALL,
                        IARG_FIRST_REP_ITERATION,
                        IARG_UINT32, ins_indx,
                        //IARG_PTR, rtn_name_str,
                        IARG_END);
                INS_InsertThenPredicatedCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR)r2m_xfer_opbn,
                        IARG_FAST_ANALYSIS_CALL,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_MEMORYWRITE_EA,
                        IARG_REG_VALUE, INS_RepCountRegister(ins),
                        IARG_REG_VALUE, INS_OperandReg(ins, OP_4),
                        IARG_UINT32, ins_indx,
                        //IARG_PTR, rtn_name_str,
                        IARG_END);
            }
            /* no rep prefix */
            else
#endif
                /* the instruction is not rep prefixed */
                INS_InsertPredicatedCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR)r2m_xfer_opb_l,
                        IARG_FAST_ANALYSIS_CALL,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_MEMORYWRITE_EA,
                        IARG_UINT32, REG8_INDX(REG_AL),
                        IARG_UINT32, ins_indx,
                        //IARG_PTR, rtn_name_str,
                        IARG_END);

            /* done */
            break;
            /* 
             * stosw; 
             * the opposite of lodsw; however, since the instruction can
             * also be prefixed with 'rep', the analysis code moves the
             * tag information, accordingly, only once (i.e., before the
             * first repetition) -- typically this will not lead in
             * inlined code
             */
        case XED_ICLASS_STOSW:
#if 0
            /* the instruction is rep prefixed */
            if (INS_RepPrefix(ins)) {
                /* propagate the tag accordingly */
                INS_InsertIfPredicatedCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR)rep_predicate,
                        IARG_FAST_ANALYSIS_CALL,
                        IARG_FIRST_REP_ITERATION,
                        IARG_UINT32, ins_indx,
                        //IARG_PTR, rtn_name_str,
                        IARG_END);
                INS_InsertThenPredicatedCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR)r2m_xfer_opwn,
                        IARG_FAST_ANALYSIS_CALL,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_MEMORYWRITE_EA,
                        IARG_REG_VALUE, INS_RepCountRegister(ins),
                        IARG_REG_VALUE, INS_OperandReg(ins, OP_4),
                        IARG_UINT32, ins_indx,
                        //IARG_PTR, rtn_name_str,
                        IARG_END);
            }
            /* no rep prefix */
            else
#endif
                /* the instruction is not rep prefixed */
                INS_InsertPredicatedCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR)r2m_xfer_opw,
                        IARG_FAST_ANALYSIS_CALL,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_MEMORYWRITE_EA,
                        IARG_UINT32, REG16_INDX(REG_AX),
                        IARG_UINT32, ins_indx,
                        //IARG_PTR, rtn_name_str,
                        IARG_END);

            /* done */
            break;
            /* 
             * stosd;
             * the opposite of lodsd; however, since the instruction can
             * also be prefixed with 'rep', the analysis code moves the
             * tag information, accordingly, only once (i.e., before the
             * first repetition) -- typically this will not lead in
             * inlined code
             */
        case XED_ICLASS_STOSD:
#if 0
            /* the instruction is rep prefixed */
            if (INS_RepPrefix(ins)) {
                /* propagate the tag accordingly */
                INS_InsertIfPredicatedCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR)rep_predicate,
                        IARG_FAST_ANALYSIS_CALL,
                        IARG_FIRST_REP_ITERATION,
                        IARG_UINT32, ins_indx,
                        //IARG_PTR, rtn_name_str,
                        IARG_END);
                INS_InsertThenPredicatedCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR)r2m_xfer_opln,
                        IARG_FAST_ANALYSIS_CALL,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_MEMORYWRITE_EA,
                        IARG_REG_VALUE, INS_RepCountRegister(ins),
                        IARG_REG_VALUE, INS_OperandReg(ins, OP_4),
                        IARG_UINT32, ins_indx,
                        //IARG_PTR, rtn_name_str,
                        IARG_END);
            }
            /* no rep prefix */
            else
#endif
                INS_InsertPredicatedCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR)r2m_xfer_opl,
                        IARG_FAST_ANALYSIS_CALL,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_MEMORYWRITE_EA,
                        IARG_UINT32, REG64_INDX(REG_EAX),
                        IARG_UINT32, ins_indx,
                        //IARG_PTR, rtn_name_str,
                        IARG_END);

            /* done */
            break;
        case XED_ICLASS_STOSQ:
            INS_InsertPredicatedCall(ins,
                    IPOINT_BEFORE,
                    (AFUNPTR)r2m_xfer_opll,
                    IARG_FAST_ANALYSIS_CALL,
                    IARG_REG_VALUE, thread_ctx_ptr,
                    IARG_MEMORYWRITE_EA,
                    IARG_UINT32, REG64_INDX(REG_GAX),
                    IARG_UINT32, ins_indx,
                    //IARG_PTR, rtn_name_str,
                    IARG_END);
            break;

            ///////////// MOVxx Instructions //////////////////////////////////

        case XED_ICLASS_MOVSQ:
            INS_InsertCall(ins,
                    IPOINT_BEFORE,
                    (AFUNPTR)m2m_xfer_opll,
                    IARG_FAST_ANALYSIS_CALL,
                    IARG_MEMORYWRITE_EA,
                    IARG_MEMORYREAD_EA,
                    IARG_UINT32, ins_indx,
                    //IARG_PTR, rtn_name_str,
                    IARG_END);

            /* done */
            break;
            /* movsd */
        case XED_ICLASS_MOVSD:
            /* the instruction is rep prefixed */
            if (INS_RepPrefix(ins)) {
                /* propagate the tag accordingly */
                INS_InsertIfPredicatedCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR)rep_predicate,
                        IARG_FAST_ANALYSIS_CALL,
                        IARG_FIRST_REP_ITERATION,
                        IARG_UINT32, ins_indx,
                        //IARG_PTR, rtn_name_str,
                        IARG_END);
                INS_InsertThenPredicatedCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR)m2m_xfer_opln,
                        IARG_FAST_ANALYSIS_CALL,
                        IARG_MEMORYWRITE_EA,
                        IARG_MEMORYREAD_EA,
                        IARG_REG_VALUE, INS_RepCountRegister(ins),
                        IARG_REG_VALUE, REG_GFLAGS,
                        IARG_UINT32, ins_indx,
                        //IARG_PTR, rtn_name_str,
                        IARG_END);
            }
            /* no rep prefix */
            else 
                /* propagate the tag accordingly */
                INS_InsertCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR)m2m_xfer_opl,
                        IARG_FAST_ANALYSIS_CALL,
                        IARG_MEMORYWRITE_EA,
                        IARG_MEMORYREAD_EA,
                        IARG_UINT32, ins_indx,
                        //IARG_PTR, rtn_name_str,
                        IARG_END);

            /* done */
            break;
            /* movsw */
        case XED_ICLASS_MOVSW:
            /* the instruction is rep prefixed */
            if (INS_RepPrefix(ins)) {
                /* propagate the tag accordingly */
                INS_InsertIfPredicatedCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR)rep_predicate,
                        IARG_FAST_ANALYSIS_CALL,
                        IARG_FIRST_REP_ITERATION,
                        IARG_UINT32, ins_indx,
                        //IARG_PTR, rtn_name_str,
                        IARG_END);
                INS_InsertThenPredicatedCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR)m2m_xfer_opwn,
                        IARG_FAST_ANALYSIS_CALL,
                        IARG_MEMORYWRITE_EA,
                        IARG_MEMORYREAD_EA,
                        IARG_REG_VALUE, INS_RepCountRegister(ins),
                        IARG_REG_VALUE, REG_GFLAGS,
                        IARG_UINT32, ins_indx,
                        //IARG_PTR, rtn_name_str,
                        IARG_END);
            }
            /* no rep prefix */
            else 
                /* propagate the tag accordingly */
                INS_InsertCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR)m2m_xfer_opw,
                        IARG_FAST_ANALYSIS_CALL,
                        IARG_MEMORYWRITE_EA,
                        IARG_MEMORYREAD_EA,
                        IARG_UINT32, ins_indx,
                        //IARG_PTR, rtn_name_str,
                        IARG_END);

            /* done */
            break;
            /* movsb */
        case XED_ICLASS_MOVSB:
            /* the instruction is rep prefixed */
            if (INS_RepPrefix(ins)) {
                /* propagate the tag accordingly */
                INS_InsertIfPredicatedCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR)rep_predicate,
                        IARG_FAST_ANALYSIS_CALL,
                        IARG_FIRST_REP_ITERATION,
                        IARG_UINT32, ins_indx,
                        //IARG_PTR, rtn_name_str,
                        IARG_END);
                INS_InsertThenPredicatedCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR)m2m_xfer_opbn,
                        IARG_FAST_ANALYSIS_CALL,
                        IARG_MEMORYWRITE_EA,
                        IARG_MEMORYREAD_EA,
                        IARG_REG_VALUE, INS_RepCountRegister(ins),
                        IARG_REG_VALUE, REG_GFLAGS,
                        IARG_UINT32, ins_indx,
                        //IARG_PTR, rtn_name_str,
                        IARG_END);
            }
            /* no rep prefix */
            else 
                /* propagate the tag accordingly */
                INS_InsertCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR)m2m_xfer_opb,
                        IARG_FAST_ANALYSIS_CALL,
                        IARG_MEMORYWRITE_EA,
                        IARG_MEMORYREAD_EA,
                        IARG_UINT32, ins_indx,
                        //IARG_PTR, rtn_name_str,
                        IARG_END);

            /* done */
            break;
            /* sal */
        case XED_ICLASS_SALC:
            /* propagate the tag accordingly */
            INS_InsertCall(ins,
                    IPOINT_BEFORE,
                    (AFUNPTR)r_clrb_l,
                    IARG_FAST_ANALYSIS_CALL,
                    IARG_REG_VALUE, thread_ctx_ptr,
                    IARG_UINT32, REG8_INDX(REG_AL),
                    IARG_UINT32, ins_indx,
                    //IARG_PTR, rtn_name_str,
                    IARG_END);

            /* done */
            break;
        
        /* pop; mov equivalent (see above) */
        case XED_ICLASS_POP:
            /* register operand */
            if (INS_OperandIsReg(ins, OP_1)) {
                /* extract the operand */
                dst_reg = INS_OperandReg(ins, OP_1);

                /* 64-bit operand */
                if (REG_is_gr64(dst_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)m2r_xfer_opll,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG64_INDX(dst_reg),
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 32-bit operand */
                else if (REG_is_gr32(dst_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)m2r_xfer_opl,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG64_INDX(dst_reg),
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 16-bit operand */
                else
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)m2r_xfer_opw,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG16_INDX(dst_reg),
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
            }
            /* memory operand */
            else if (INS_OperandIsMemory(ins, OP_1)) {
                /* 64-bit operand */
                if (INS_MemoryWriteSize(ins) ==
                        BIT2BYTE(MEM_LLONG_LEN))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)m2m_xfer_opll,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_MEMORYWRITE_EA,
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 32-bit operand */
                if (INS_MemoryWriteSize(ins) ==
                        BIT2BYTE(MEM_LONG_LEN))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)m2m_xfer_opl,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_MEMORYWRITE_EA,
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 16-bit operand */
                else
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)m2m_xfer_opw,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_MEMORYWRITE_EA,
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
            }

            /* done */
            break;
            /* push; mov equivalent (see above) */
        case XED_ICLASS_PUSH:
            /* register operand */
            if (INS_OperandIsReg(ins, OP_1)) {
                /* extract the operand */
                src_reg = INS_OperandReg(ins, OP_1);

                /* 64-bit operand */
                if (REG_is_gr64(src_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2m_xfer_opll,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, REG64_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 32-bit operand */
                else if (REG_is_gr32(src_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2m_xfer_opl,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, REG64_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 16-bit operand */
                else
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2m_xfer_opw,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, REG16_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
            }
            /* memory operand */
            else if (INS_OperandIsMemory(ins, OP_1)) {
                /* 64-bit operand */
                if (INS_MemoryWriteSize(ins) ==
                        BIT2BYTE(MEM_LLONG_LEN))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)m2m_xfer_opll,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_MEMORYWRITE_EA,
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 32-bit operand */
                if (INS_MemoryWriteSize(ins) ==
                        BIT2BYTE(MEM_LONG_LEN))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)m2m_xfer_opl,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_MEMORYWRITE_EA,
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 16-bit operand */
                else
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)m2m_xfer_opw,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_MEMORYWRITE_EA,
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
            }
            /* immediate or segment operand; clean */
            else {
                /* clear n-bytes */
                switch (INS_OperandWidth(ins, OP_1)) {
                    /* 4 bytes */
                    case MEM_LLONG_LEN:
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)ins_clrll,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_MEMORYWRITE_EA,
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);
                        /* 4 bytes */
                    case MEM_LONG_LEN:
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)ins_clrl,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_MEMORYWRITE_EA,
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);

                        /* done */
                        break;
                        /* 2 bytes */
                    case MEM_WORD_LEN:
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)ins_clrw,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_MEMORYWRITE_EA,
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);

                        /* done */
                        break;
                        /* 1 byte */
                    case MEM_BYTE_LEN:
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)ins_clrb,
                                IARG_FAST_ANALYSIS_CALL,
                                IARG_MEMORYWRITE_EA,
                                IARG_UINT32, ins_indx,
                                //IARG_PTR, rtn_name_str,
                                IARG_END);

                        /* done */
                        break;
                        /* make the compiler happy */
                    default:
                        /* done */
                        break;
                }
            }

            /* done */
            break;
            /* popa;
             * similar to pop but for all the 16-bit
             * general purpose registers
             */
        case XED_ICLASS_POPA:
            /* propagate the tag accordingly */
            INS_InsertCall(ins,
                    IPOINT_BEFORE,
                    (AFUNPTR)m2r_restore_opw,
                    IARG_FAST_ANALYSIS_CALL,
                    IARG_REG_VALUE, thread_ctx_ptr,
                    IARG_MEMORYREAD_EA,
                    IARG_UINT32, ins_indx,
                    //IARG_PTR, rtn_name_str,
                    IARG_END);

            /* done */
            break;
            /* popad; 
             * similar to pop but for all the 32-bit
             * general purpose registers
             */
        case XED_ICLASS_POPAD:
            /* propagate the tag accordingly */
            INS_InsertCall(ins,
                    IPOINT_BEFORE,
                    (AFUNPTR)m2r_restore_opl,
                    IARG_FAST_ANALYSIS_CALL,
                    IARG_REG_VALUE, thread_ctx_ptr,
                    IARG_MEMORYREAD_EA,
                    IARG_UINT32, ins_indx,
                    //IARG_PTR, rtn_name_str,
                    IARG_END);

            /* done */
            break;

            /* pusha; 
             * similar to push but for all the 16-bit
             * general purpose registers
             */
        case XED_ICLASS_PUSHA:
            /* propagate the tag accordingly */
            INS_InsertCall(ins,
                    IPOINT_BEFORE,
                    (AFUNPTR)r2m_save_opw,
                    IARG_FAST_ANALYSIS_CALL,
                    IARG_REG_VALUE, thread_ctx_ptr,
                    IARG_MEMORYWRITE_EA,
                    IARG_UINT32, ins_indx,
                    //IARG_PTR, rtn_name_str,
                    IARG_END);

            /* done */
            break;
            /* pushad; 
             * similar to push but for all the 32-bit
             * general purpose registers
             */
        case XED_ICLASS_PUSHAD:
            /* propagate the tag accordingly */
            INS_InsertCall(ins,
                    IPOINT_BEFORE,
                    (AFUNPTR)r2m_save_opl,
                    IARG_FAST_ANALYSIS_CALL,
                    IARG_REG_VALUE, thread_ctx_ptr,
                    IARG_MEMORYWRITE_EA,
                    IARG_UINT32, ins_indx,
                    //IARG_PTR, rtn_name_str,
                    IARG_END);

            /* done */
            break;
            /* pushf; clear a memory word (i.e., 16-bits) */
        case XED_ICLASS_PUSHF:
            /* propagate the tag accordingly */
            INS_InsertCall(ins,
                    IPOINT_BEFORE,
                    (AFUNPTR)ins_clrw,
                    IARG_FAST_ANALYSIS_CALL,
                    IARG_MEMORYWRITE_EA,
                    IARG_UINT32, ins_indx,
                    //IARG_PTR, rtn_name_str,
                    IARG_END);

            /* done */
            break;
            /* pushfd; clear a double memory word (i.e., 32-bits) */
        case XED_ICLASS_PUSHFD:
            /* propagate the tag accordingly */
            INS_InsertCall(ins,
                    IPOINT_BEFORE,
                    (AFUNPTR)ins_clrl,
                    IARG_FAST_ANALYSIS_CALL,
                    IARG_MEMORYWRITE_EA,
                    IARG_UINT32, ins_indx,
                    //IARG_PTR, rtn_name_str,
                    IARG_END);

            /* done */
            break;
            /* pushfq; clear a quad memory word (i.e., 32-bits) */
        case XED_ICLASS_PUSHFQ:
            /* propagate the tag accordingly */
            INS_InsertCall(ins,
                    IPOINT_BEFORE,
                    (AFUNPTR)ins_clrll,
                    IARG_FAST_ANALYSIS_CALL,
                    IARG_MEMORYWRITE_EA,
                    IARG_UINT32, ins_indx,
                    //IARG_PTR, rtn_name_str,
                    IARG_END);

            /* done */
            break;

            /* call (near);  pushes EIP on the stack*/
        case XED_ICLASS_CALL_NEAR:
        case XED_ICLASS_CALL_FAR:
            assert(REG_Width(REG_INST_PTR) == REGWIDTH_64);
            if(INS_MemoryWriteSize(ins) == BIT2BYTE(MEM_LLONG_LEN << 1))
                INS_InsertCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR)ins_clrn,
                        IARG_FAST_ANALYSIS_CALL,
                        IARG_MEMORYWRITE_EA,
                        IARG_MEMORYWRITE_SIZE,
                        IARG_UINT32, ins_indx,
                        //IARG_PTR, rtn_name_str,
                        IARG_END);
            else if(INS_MemoryWriteSize(ins) == BIT2BYTE(MEM_LLONG_LEN))
                INS_InsertCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR)ins_clrll,
                        IARG_FAST_ANALYSIS_CALL,
                        IARG_MEMORYWRITE_EA,
                        IARG_UINT32, ins_indx,
                        //IARG_PTR, rtn_name_str,
                        IARG_END);
            else if(INS_MemoryWriteSize(ins) == BIT2BYTE(MEM_LONG_LEN))
                INS_InsertCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR)ins_clrl,
                        IARG_FAST_ANALYSIS_CALL,
                        IARG_MEMORYWRITE_EA,
                        IARG_UINT32, ins_indx,
                        //IARG_PTR, rtn_name_str,
                        IARG_END);
            break;
            // TODO: I'm pretty sure what they had was wrong - verify this
#if 0

            /* relative target */
            if (INS_OperandIsImmediate(ins, OP_0)) {
                /* 32-bit operand */
                if (INS_OperandWidth(ins, OP_0) == MEM_LONG_LEN)
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)ins_clrl,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 16-bit operand */
                else
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)ins_clrw,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
            }
            /* absolute target; register */
            else if (INS_OperandIsReg(ins, OP_0)) {
                /* extract the source register */
                src_reg = INS_OperandReg(ins, OP_0);

                /* 32-bit operand */
                if (REG_is_gr32(src_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)ins_clrl,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 16-bit operand */
                else
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)ins_clrw,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
            }
            /* absolute target; memory */
            else {
                /* 32-bit operand */
                if (INS_OperandWidth(ins, OP_0) == MEM_LONG_LEN)
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)ins_clrl,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);

                /* 16-bit operand */
                else
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)ins_clrw,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
            }

            /* done */
            break;
#endif

            /* 
             * leave;
             * similar to a mov between ESP/SP and EBP/BP, and a pop
             */
        case XED_ICLASS_LEAVE:
			dst_reg = INS_OperandReg(ins, OP_2);

            if (REG_is_gr64(dst_reg)) {
                /* propagate the tag accordingly */
                INS_InsertCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR)r2r_xfer_opl,
                        IARG_FAST_ANALYSIS_CALL,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, REG_STACK_PTR,
                        IARG_UINT32, REG_GBP,
                        IARG_UINT32, ins_indx,
                        //IARG_PTR, rtn_name_str,
                        IARG_END);
                INS_InsertCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR)m2r_xfer_opll,
                        IARG_FAST_ANALYSIS_CALL,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, REG_GBP,
                        IARG_MEMORYREAD_EA,
                        IARG_UINT32, ins_indx,
                        //IARG_PTR, rtn_name_str,
                        IARG_END);
            }
            else if (REG_is_gr32(dst_reg)) {
                /* propagate the tag accordingly */
                INS_InsertCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR)r2r_xfer_opl,
                        IARG_FAST_ANALYSIS_CALL,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, REG_ESP,
                        IARG_UINT32, REG_EBP,
                        IARG_UINT32, ins_indx,
                        //IARG_PTR, rtn_name_str,
                        IARG_END);
                INS_InsertCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR)m2r_xfer_opl,
                        IARG_FAST_ANALYSIS_CALL,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, REG_EBP,
                        IARG_MEMORYREAD_EA,
                        IARG_UINT32, ins_indx,
                        //IARG_PTR, rtn_name_str,
                        IARG_END);
            }
            /* 16-bit operands */
            else {
                /* propagate the tag accordingly */
                INS_InsertCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR)r2r_xfer_opw,
                        IARG_FAST_ANALYSIS_CALL,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, REG_ESP,
                        IARG_UINT32, REG_EBP,
                        IARG_UINT32, ins_indx,
                        //IARG_PTR, rtn_name_str,
                        IARG_END);
                INS_InsertCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR)m2r_xfer_opw,
                        IARG_FAST_ANALYSIS_CALL,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, REG_EBP,
                        IARG_MEMORYREAD_EA,
                        IARG_UINT32, ins_indx,
                        //IARG_PTR, rtn_name_str,
                        IARG_END);
            }

            /* done */
            break;

            /* lea */
        case XED_ICLASS_LEA:
            /*
             * the general format of this instruction
             * is the following: dst = src_base | src_indx.
             * We move the tags of the source base and index
             * registers to the destination
             * (i.e., t[dst] = t[src_base] | t[src_indx])
             */

            /* extract the operands */
            reg_base	= INS_MemoryBaseReg(ins);
            reg_indx	= INS_MemoryIndexReg(ins);
            dst_reg		= INS_OperandReg(ins, OP_1);

            /* no base or index register; clear the destination */
            if (reg_base == REG_INVALID() &&
                    reg_indx == REG_INVALID()) {
                /* 32/64-bit operands */
                if (REG_is_gr64(dst_reg) || REG_is_gr32(dst_reg))
                    /* clear */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r_clrl,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG64_INDX(dst_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 16-bit operands */
                else 
                    /* clear */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r_clrw,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG16_INDX(dst_reg),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
            }
            /* base register exists; no index register */
            if (reg_base != REG_INVALID() &&
                    reg_indx == REG_INVALID()) {
                /* 32/64-bit operands */
                if (REG_is_gr64(dst_reg) || REG_is_gr32(dst_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2r_xfer_opl,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG64_INDX(dst_reg),
                            IARG_UINT32, REG64_INDX(reg_base),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 16-bit operands */
                else 
                    /* propagate tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2r_xfer_opw,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG16_INDX(dst_reg),
                            IARG_UINT32, REG16_INDX(reg_base),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
            }
            /* index register exists; no base register */
            if (reg_base == REG_INVALID() &&
                    reg_indx != REG_INVALID()) {
                /* 32/64-bit operands */
                if (REG_is_gr64(dst_reg) || REG_is_gr32(dst_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2r_xfer_opl,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG64_INDX(dst_reg),
                            IARG_UINT32, REG64_INDX(reg_indx),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 16-bit operands */
                else
                    /* propagate tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)r2r_xfer_opw,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG16_INDX(dst_reg),
                            IARG_UINT32, REG16_INDX(reg_indx),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
            }
            /* base and index registers exist */
            if (reg_base != REG_INVALID() &&
                    reg_indx != REG_INVALID()) {
                /* 32/64-bit operands */
                if (REG_is_gr64(dst_reg) || REG_is_gr32(dst_reg))
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)_lea_r2r_opl,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG64_INDX(dst_reg),
                            IARG_UINT32, REG64_INDX(reg_base),
                            IARG_UINT32, REG64_INDX(reg_indx),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
                /* 16-bit operands */
                else
                    /* propagate the tag accordingly */
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR)_lea_r2r_opw,
                            IARG_FAST_ANALYSIS_CALL,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, REG16_INDX(dst_reg),
                            IARG_UINT32, REG16_INDX(reg_base),
                            IARG_UINT32, REG16_INDX(reg_indx),
                            IARG_UINT32, ins_indx,
                            //IARG_PTR, rtn_name_str,
                            IARG_END);
            }

            /* done */
            break;



        //new instructions://///////////////////////////////

            //CHECK - 
        case XED_ICLASS_XGETBV:
            INS_InsertCall(ins, IPOINT_BEFORE,
                    (AFUNPTR) r_clrl2,
                    IARG_REG_VALUE, thread_ctx_ptr,
                    IARG_UINT32, ins_indx,
                    IARG_END);
            break;

        /* These instructions have taint propagation of the form 
         * t[dst] |= t[src]
         * MMX and SSE versions: the upper 128 bits of dst XMM registers are
         * not modified
         */
        case XED_ICLASS_PXOR:
        case XED_ICLASS_POR:
        case XED_ICLASS_XORPS:
        case XED_ICLASS_PSUBB:
        case XED_ICLASS_PSUBW:
        case XED_ICLASS_PSUBD:
        case XED_ICLASS_PSUBQ:
        case XED_ICLASS_PSUBSB:
        case XED_ICLASS_PSUBSW:
        case XED_ICLASS_PCMPEQB:
        case XED_ICLASS_PCMPEQW:
        case XED_ICLASS_PCMPEQD:
        case XED_ICLASS_PCMPGTD:
        case XED_ICLASS_PAND:
        case XED_ICLASS_PANDN:
        case XED_ICLASS_PADDB:
        case XED_ICLASS_PADDW:
        case XED_ICLASS_PADDD:
        case XED_ICLASS_PADDQ:
        case XED_ICLASS_PMINUB:
        case XED_ICLASS_ADDSD:
        //note: no need to track aesenc bc always followed by aesenclast
        case XED_ICLASS_AESENCLAST: 
            // dst is always a register
            dst_reg = INS_OperandReg(ins, OP_1);

            // MMX registers
            if(REG_is_mm(dst_reg))
            {
                // Both operands registers
                if(INS_MemoryOperandCount(ins) == 0)
                {
                    src_reg = INS_OperandReg(ins, OP_2);
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR) mm2mm_union_2op64,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, MM_INDX(dst_reg),
                            IARG_UINT32, MM_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            IARG_END);
                }
                // Src is 64-bit memory location
                else
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR) m2mm_union_2op64,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, MM_INDX(dst_reg),
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            IARG_END);
            }

            // XMM registers
            else
            {
                // Src is 128-bit memory location
                if(INS_MemoryOperandCount(ins) == 1)
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR) m2xmm_union_2op128,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, XMM_INDX(dst_reg),
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            IARG_END);
                // Two register operands 
                else
                { 
                    src_reg = INS_OperandReg(ins, OP_2);
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR) xmm2xmm_union_2op128,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, XMM_INDX(dst_reg),
                            IARG_UINT32, XMM_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            IARG_END);
                }
            }
            break;

        /* These are AVX instructions with two source operands that have 
         * taint propagation of the form:
         *      t[dst] = t[src1] | t[src2]
         * The upper bits of dst register operands are zeroed. 
         */
        case XED_ICLASS_VPXOR:
        case XED_ICLASS_VPXORD:
        case XED_ICLASS_VPXORQ:
        case XED_ICLASS_VPOR:
        case XED_ICLASS_VPORD:
        case XED_ICLASS_VPORQ:
        case XED_ICLASS_VPSUBB:
        case XED_ICLASS_VPSUBD:
        case XED_ICLASS_VPSUBQ:
        case XED_ICLASS_VPSUBSB:
        case XED_ICLASS_VPSUBSW:
        case XED_ICLASS_VPCMPEQB:
        case XED_ICLASS_VPCMPEQW:
        case XED_ICLASS_VPCMPEQD:
        case XED_ICLASS_VPCMPGTB:
        case XED_ICLASS_VPCMPGTW:
        case XED_ICLASS_VPCMPGTD:
        case XED_ICLASS_VPAND:
        case XED_ICLASS_VPANDD:
        case XED_ICLASS_VPANDN:
        case XED_ICLASS_VPANDND:
        case XED_ICLASS_VPADDB:
        case XED_ICLASS_VPADDW:
        case XED_ICLASS_VPADDD:
        case XED_ICLASS_VPADDQ:
        case XED_ICLASS_VORPD:
            // Dst is always a register- TODO: check this
            dst_reg = INS_OperandReg(ins, OP_1);
            // XMM registers
            if(REG_is_xmm(dst_reg))
            {
                src1_reg = INS_OperandReg(ins, OP_2);
                // src2 is 128-bit memory location
                if(INS_MemoryOperandCount(ins) == 1)
                {
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR) xmm_m2xmm_src_union_3op128_zero_upper,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, XMM_INDX(dst_reg),
                            IARG_UINT32, XMM_INDX(src1_reg),
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            IARG_END);
                }
                // Two register source operands 
                else 
                {
                    src2_reg = INS_OperandReg(ins, OP_3);
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR) xmm_xmm2xmm_src_union_3op128_zero_upper,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, XMM_INDX(dst_reg),
                            IARG_UINT32, XMM_INDX(src1_reg),
                            IARG_UINT32, XMM_INDX(src2_reg),
                            IARG_UINT32, ins_indx,
                            IARG_END);
                }
            }
            // YMM registers
            else if(REG_is_ymm(dst_reg))
            {
                src1_reg = INS_OperandReg(ins, OP_2);
                // src2 is 128-bit memory location
                if(INS_MemoryOperandCount(ins) == 1)
                {
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR) ymm_m2ymm_src_union_3op256,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, YMM_INDX(dst_reg),
                            IARG_UINT32, YMM_INDX(src1_reg),
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            IARG_END);
                }
                // Two register source operands 
                else 
                {
                    src2_reg = INS_OperandReg(ins, OP_3);
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR) ymm_ymm2ymm_src_union_3op256,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, YMM_INDX(dst_reg),
                            IARG_UINT32, YMM_INDX(src1_reg),
                            IARG_UINT32, YMM_INDX(src2_reg),
                            IARG_UINT32, ins_indx,
                            IARG_END);
                }
            }
            else
                printLog("Unhandled operand type: %s\n",
                        INS_Disassemble(ins));

            break;
        
        /* These instructions move d/qword between two of mem, 32/64-bit gpr,
         * mmx or xmm registers (but not between two of the same)
         * with taint propagation of the form:
         *      t[dst] = t[src]
         * For AVX version, upper bits are zeroed. For SSE, upper bits not 
         * modified.
         *  (V)MOVD, (V)MOVQ
         */
        case XED_ICLASS_MOVD:
        case XED_ICLASS_VMOVD:
            /* Forms:
             * mm, r/m32 *Upper 32 bits zeroed
             * r/m32, mm
             * xmm, r/m32 *Zeroed to 128 bits for MOVD, to 256 bits for VMOVD 
             * r/m32, xmm
             */
            // Dst is reg: mm, xmm, or gpr
            if(INS_OperandIsReg(ins, OP_1))
            {
                dst_reg = INS_OperandReg(ins, OP_1);
                // src is also reg: mm, xmm, gpr
                if(INS_OperandIsReg(ins, OP_2))
                {
                    src_reg = INS_OperandReg(ins, OP_2);
                    // mm, r
                    if(REG_is_mm(dst_reg))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR) r2mm_xfer_2op32_zx64,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, MM_INDX(dst_reg),
                                IARG_UINT32, REG64_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    // xmm, r
                    else if(REG_is_xmm(dst_reg))
                    {
                        // MOVD: zero dst to 128 bits, upper 128 unmodified
                        if(ins_indx == XED_ICLASS_MOVD)
                            INS_InsertCall(ins,
                                    IPOINT_BEFORE,
                                    (AFUNPTR) r2xmm_xfer_2op32_zx128,
                                    IARG_REG_VALUE, thread_ctx_ptr,
                                    IARG_UINT32, XMM_INDX(dst_reg),
                                    IARG_UINT32, REG64_INDX(src_reg),
                                    IARG_UINT32, ins_indx,
                                    IARG_END);
                        // VMOVD: zero to 256 bits
                        else
                            INS_InsertCall(ins,
                                    IPOINT_BEFORE,
                                    (AFUNPTR) r2xmm_xfer_2op32_zx256,
                                    IARG_REG_VALUE, thread_ctx_ptr,
                                    IARG_UINT32, XMM_INDX(dst_reg),
                                    IARG_UINT32, REG64_INDX(src_reg),
                                    IARG_UINT32, ins_indx,
                                    IARG_END);
                    }
                    // else dst is gpr
                    else
                    {
                        //r, mm
                        if(REG_is_mm(src_reg))
                            INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR) mm2r_xfer_2op32,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT32, MM_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                        //r, xmm
                        else
                            INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR) xmm2r_xfer_2op32,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT32, XMM_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    }
                }
                // src is 32-bit memory location
                else
                {
                    // dst is mmx reg
                    if(REG_is_mm(dst_reg))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR) m2mm_xfer_2op32_zx64,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, MM_INDX(dst_reg),
                                IARG_MEMORYREAD_EA,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    // dst is xmm reg
                    else
                    {
                        //MOVD: zero to 128 bits, upper 128 unmodified
                        if(ins_indx == XED_ICLASS_MOVD)
                            INS_InsertCall(ins,
                                    IPOINT_BEFORE,
                                    (AFUNPTR) m2xmm_xfer_2op32_zx128,
                                    IARG_REG_VALUE, thread_ctx_ptr,
                                    IARG_UINT32, XMM_INDX(dst_reg),
                                    IARG_MEMORYREAD_EA,
                                    IARG_UINT32, ins_indx,
                                    IARG_END);
                        // VMOVD: zero full 256 bits 
                        else
                            INS_InsertCall(ins,
                                    IPOINT_BEFORE,
                                    (AFUNPTR) m2xmm_xfer_2op32_zx256,
                                    IARG_REG_VALUE, thread_ctx_ptr,
                                    IARG_UINT32, XMM_INDX(dst_reg),
                                    IARG_MEMORYREAD_EA,
                                    IARG_UINT32, ins_indx,
                                    IARG_END);
                    }
                }
            }
            // dst is memory location
            else
            {
                src_reg = INS_OperandReg(ins, OP_2); 
                // dst is mmx reg
                if(REG_is_mm(src_reg))
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR) mm2m_xfer_2op32,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, MM_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            IARG_END);
                // dst is xmm reg
                else
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR) xmm2m_xfer_2op32,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, XMM_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            IARG_END);
            }
            break;

        case XED_ICLASS_MOVQ:
        case XED_ICLASS_VMOVQ:
            /* Forms:
             * mm, r/m64 
             * r/m32, mm
             * xmm, r/m64 *Zeroed to 128 bits for MOVQ, to 256 bits for VMOVQ 
             * r/m32, xmm
             */
            // Dst is reg: mm, xmm, or gpr
            if(INS_OperandIsReg(ins, OP_1))
            {
                dst_reg = INS_OperandReg(ins, OP_1);
                // src is also reg: mm, xmm, gpr
                if(INS_OperandIsReg(ins, OP_2))
                {
                    src_reg = INS_OperandReg(ins, OP_2);
                    // mm, r
                    if(REG_is_mm(dst_reg))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR) r2mm_xfer_2op64,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, MM_INDX(dst_reg),
                                IARG_UINT32, REG64_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    // xmm, r
                    else if(REG_is_xmm(dst_reg))
                    {
                        // MOVQ: zero dst to 128 bits, upper 128 unmodified
                        if(ins_indx == XED_ICLASS_MOVQ)
                            INS_InsertCall(ins,
                                    IPOINT_BEFORE,
                                    (AFUNPTR) r2xmm_xfer_2op64_zx128,
                                    IARG_REG_VALUE, thread_ctx_ptr,
                                    IARG_UINT32, XMM_INDX(dst_reg),
                                    IARG_UINT32, REG64_INDX(src_reg),
                                    IARG_UINT32, ins_indx,
                                    IARG_END);
                        // VMOVQ: zero to 256 bits
                        else
                            INS_InsertCall(ins,
                                    IPOINT_BEFORE,
                                    (AFUNPTR) r2xmm_xfer_2op64_zx256,
                                    IARG_REG_VALUE, thread_ctx_ptr,
                                    IARG_UINT32, XMM_INDX(dst_reg),
                                    IARG_UINT32, REG64_INDX(src_reg),
                                    IARG_UINT32, ins_indx,
                                    IARG_END);
                    }
                    // else dst is gpr
                    else
                    {
                        //r, mm
                        if(REG_is_mm(src_reg))
                            INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR) mm2r_xfer_2op64,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT32, XMM_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                        //r, xmm
                        else
                            INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR) xmm2r_xfer_2op64,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT32, XMM_INDX(src_reg),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    }
                }
                // src is 32-bit memory location
                else
                {
                    // dst is mmx reg
                    if(REG_is_mm(dst_reg))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR) m2mm_xfer_2op64,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, MM_INDX(dst_reg),
                                IARG_MEMORYREAD_EA,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    // dst is xmm reg
                    else
                    {
                        //MOVQ: zero to 128 bits, upper 128 unmodified
                        if(ins_indx == XED_ICLASS_MOVQ)
                            INS_InsertCall(ins,
                                    IPOINT_BEFORE,
                                    (AFUNPTR) m2xmm_xfer_2op64_zx128,
                                    IARG_REG_VALUE, thread_ctx_ptr,
                                    IARG_UINT32, XMM_INDX(dst_reg),
                                    IARG_MEMORYREAD_EA,
                                    IARG_UINT32, ins_indx,
                                    IARG_END);
                        // VMOVQ: zero full 256 bits 
                        else
                            INS_InsertCall(ins,
                                    IPOINT_BEFORE,
                                    (AFUNPTR) m2xmm_xfer_2op64_zx256,
                                    IARG_REG_VALUE, thread_ctx_ptr,
                                    IARG_UINT32, XMM_INDX(dst_reg),
                                    IARG_MEMORYREAD_EA,
                                    IARG_UINT32, ins_indx,
                                    IARG_END);
                    }
                }
            }
            // dst is memory location
            else
            {
                src_reg = INS_OperandReg(ins, OP_2); 
                // dst is mmx reg
                if(REG_is_mm(src_reg))
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR) mm2m_xfer_2op64,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, MM_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            IARG_END);
                // dst is xmm reg
                else
                    INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR) xmm2m_xfer_2op64,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, XMM_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            IARG_END);
            }
            break;
        
        /* Saves RIP into RCX, loads canonical addr into RIP, 
         * save RFLAGS ino R11
         */
        case XED_ICLASS_SYSCALL:
            INS_InsertCall(ins,
                    IPOINT_BEFORE,
                    (AFUNPTR)handle_syscall,
                    IARG_REG_VALUE, thread_ctx_ptr,
                    IARG_UINT32, ins_indx,
                    IARG_END);
            break;
        
        /* These are XMM/YMM register instructions with taint propagating
         * as t[dst] = t[src]
         */
        case XED_ICLASS_MOVDQA:
        case XED_ICLASS_VMOVDQA:
        case XED_ICLASS_MOVDQU:
        case XED_ICLASS_VMOVDQU:
        case XED_ICLASS_MOVUPS:
        case XED_ICLASS_VMOVUPS:
        case XED_ICLASS_MOVUPD:
        case XED_ICLASS_VMOVUPD:
        case XED_ICLASS_MOVAPS:
        case XED_ICLASS_MOVSD_XMM:
            //Both operands registers
            if(INS_MemoryOperandCount(ins) == 0)
            {
                dst_reg = INS_OperandReg(ins, OP_1);
                src_reg = INS_OperandReg(ins, OP_2);

                // XMM registers
                if(REG_is_xmm(dst_reg))
                {
                    //SSE version: upper 128 bits unmodified
                    if(INS_Extension(ins) == XED_EXTENSION_SSE || 
                            INS_Extension(ins) == XED_EXTENSION_SSE2)
                        INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR) xmm2xmm_xfer_2op128,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, XMM_INDX(dst_reg),
                            IARG_UINT32, XMM_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            IARG_END);
                    //AVX version: zero upper 128 bits
                    else
                        INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR) xmm2xmm_xfer_2op128_zero_upper,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, XMM_INDX(dst_reg),
                            IARG_UINT32, XMM_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            IARG_END);
                }
                // YMM registers
                else if (REG_is_ymm(dst_reg))
                        INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR) ymm2ymm_xfer_2op256,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, YMM_INDX(dst_reg),
                            IARG_UINT32, YMM_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            IARG_END);
                else
                    printLog("unhandled register type: %s\n",
                            INS_Disassemble(ins).c_str());
            }
            // Dst is reg, Src is memory location
            else if(INS_OperandIsReg(ins, OP_1))
            {
                dst_reg = INS_OperandReg(ins, OP_1);

                // XMM registers
                if(REG_is_xmm(dst_reg))
                {
                    //SSE version: upper 128 bits unmodified
                    if(INS_Extension(ins) == XED_EXTENSION_SSE2 || 
                            INS_Extension(ins) == XED_EXTENSION_SSE)
                        INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR) m2xmm_xfer_2op128,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, XMM_INDX(dst_reg),
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            IARG_END);
                    // AVX version: zero upper 128 bits
                    else
                        INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR) m2xmm_xfer_2op128_zero_upper,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, XMM_INDX(dst_reg),
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            IARG_END);
                }

                // YMM registers
                else if (REG_is_ymm(dst_reg))
                        INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR) m2ymm_xfer_2op256,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, YMM_INDX(dst_reg),
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            IARG_END);
                else
                    printLog("unhandled register type: %s\n",
                            INS_Disassemble(ins).c_str());
            }
            // Dst is memory location, Src is reg
            else
            {
                src_reg = INS_OperandReg(ins, OP_2);

                // XMM registers
                if(REG_is_xmm(src_reg))
                        INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR) xmm2m_xfer_2op128,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, XMM_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            IARG_END);
                // YMM registers
                else if (REG_is_ymm(src_reg))
                        INS_InsertCall(ins,
                            IPOINT_BEFORE,
                            (AFUNPTR) ymm2m_xfer_2op256,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_MEMORYWRITE_EA,
                            IARG_UINT32, YMM_INDX(src_reg),
                            IARG_UINT32, ins_indx,
                            IARG_END);
                else
                    printLog("unhandled register type: %s\n",
                            INS_Disassemble(ins).c_str());
            }
            break;

        case XED_ICLASS_MOVLPD:
            // load: first operand register
            if(INS_OperandIsReg(ins, OP_1))
            {
                // load m64 to low 64 bits of XMM reg
                if(INS_OperandIsMemory(ins, OP_2))
                    INS_InsertCall(ins, 
                            IPOINT_BEFORE,
                            (AFUNPTR) m64_2xmm_l_xfer_2op128_l,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_1)),
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            IARG_END);
                
                // merge m64 with high qword of xmm1 reg and load into xmm2 reg
                else
                    INS_InsertCall(ins, 
                            IPOINT_BEFORE,
                            (AFUNPTR) m64_xmm_h2xmm_xfer_2op128_l,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_1)),
                            IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            IARG_END);
            }
            // store: first operand memory location
            else
                INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) xmm_l2m64_xfer_2op128_l,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_MEMORYWRITE_EA,
                        IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT32, ins_indx,
                        IARG_END);
            break;

        case XED_ICLASS_MOVHPD:
        case XED_ICLASS_MOVHPS:
            // load: first operand register
            if(INS_OperandIsReg(ins, OP_1))
            {
                // load m64 to high 64 bits of XMM reg
                if(INS_OperandIsMemory(ins, OP_2))
                    INS_InsertCall(ins, 
                            IPOINT_BEFORE,
                            (AFUNPTR) m64_2xmm_h_xfer_2op128_h,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_1)),
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            IARG_END);
                
                // merge m64 with high qword of xmm1 reg and load into xmm2 reg
                else
                    INS_InsertCall(ins, 
                            IPOINT_BEFORE,
                            (AFUNPTR) m64_xmm_l2xmm_xfer_2op128_h,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_1)),
                            IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, ins_indx,
                            IARG_END);
            }
            // store: first operand memory location
            else
                INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) xmm_h2m64_xfer_2op128_h,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_MEMORYWRITE_EA,
                        IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT32, ins_indx,
                        IARG_END);
            break;


        /* creates mask made of msb of each byte in src op and stores in low
        * byte/word/dword of dst, which is always a gpr. The src reg can be an
        * MMX, or YMM register
        *   t[dst_low] = t[src]
        * The upper bits of the gpr are zeroed for both SSE and AVX versions
        */
        case XED_ICLASS_PMOVMSKB:
        case XED_ICLASS_VPMOVMSKB:
            src_reg = INS_OperandReg(ins, OP_1);
            dst_reg = INS_OperandReg(ins, OP_2);
            //MMX register: 64 bit src so 8-bit mask
            if(REG_is_mm(dst_reg))
                INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) mm2r_xfer_op8_zero_upper,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, MM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT32, REG64_INDX(src_reg),
                        IARG_UINT32, ins_indx,
                        IARG_END);
            // XMM register: 128 bits so 16-bit mask
            else if(REG_is_xmm(dst_reg))
                INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) xmm2r_xfer_op16_zero_upper,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT32, REG64_INDX(src_reg),
                        IARG_UINT32, ins_indx,
                        IARG_END);
            // YMM register: 256 bits so 32-bit mask
            else
                INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) ymm2r_xfer_op32_zero_upper,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, YMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT32, REG64_INDX(src_reg),
                        IARG_UINT32, ins_indx,
                        IARG_END);
            break;

        /*Shifts: shift first operand left by number of bytes in second operand.
         * SSE version: upper 128 bits of dst XMM reg unmodified
         */
        case XED_ICLASS_PSLLDQ:
            dst_reg = INS_OperandReg(ins, OP_1);
                INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftl_xmm_imm_bytes_2op128,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT64, INS_OperandImmediate(ins, OP_2),
                        IARG_UINT32, ins_indx,
                        IARG_END); 
            break;
        
        /*Shifts: shift right first operand by number of bytes in second operand.
         * SSE version: upper 128 bits of dst XMM reg unmodified
         */
        case XED_ICLASS_PSRLDQ:
            dst_reg = INS_OperandReg(ins, OP_1);
                INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftr_xmm_imm_bytes_2op128,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT64, INS_OperandImmediate(ins, OP_2),
                        IARG_UINT32, ins_indx,
                        IARG_END); 
            break;
        
        /*Shift left each dqword in the second operand by number in third operand
         * and store in first operand.
         *      t[dst[0:127]] = t[src[0:127]] << (count * 8)
         * AVX version: upper 128 bits zerod if dst XMM reg
         */
        case XED_ICLASS_VPSLLDQ:
            dst_reg = INS_OperandReg(ins, OP_1);
            // TODO: Do we need to handle mem location sources?
            if(INS_OperandIsMemory(ins, OP_2))
            {
                printLog("ERROR: missed memory operand type: %s\n",
                        INS_Disassemble(ins).c_str());
                break;
            }
            // XMM registers
            else if(REG_is_xmm(dst_reg))
                INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftl_pdq_xmm_imm_bytes_3op128_zero_upper,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                        IARG_UINT32, ins_indx,
                        IARG_END);
            // YMM registers
            else
                INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftl_pdq_ymm_imm_bytes_3op256,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                        IARG_UINT32, ins_indx,
                        IARG_END);
            break;

        /*Shift right each dqword in the second operand by number in third operand
         * and store in first operand.
         *      t[dst[0:127]] = t[src[0:127]] >> (count * 8)
         * AVX version: upper 128 bits zerod if dst XMM reg
         */
        case XED_ICLASS_VPSRLDQ:
            dst_reg = INS_OperandReg(ins, OP_1);
            // TODO: Do we need to handle mem location sources?
            if(INS_OperandIsMemory(ins, OP_2))
            {
                printLog("ERROR: missed memory operand type: %s\n",
                        INS_Disassemble(ins).c_str());
                break;
            }
            // XMM registers
            else if(REG_is_xmm(dst_reg))
                INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftr_pdq_xmm_imm_bytes_3op128_zero_upper,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                        IARG_UINT32, ins_indx,
                        IARG_END);
            // YMM registers
            else
                INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftr_pdq_ymm_imm_bytes_3op256,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                        IARG_UINT32, ins_indx,
                        IARG_END);
            break;

        /* shift packed words left/right by count bits
         *      t[dst[0:15]] = t[dst[0:15]] <</>> count
         * upper 128 bits unmodified for dst xmm register
         */
        case XED_ICLASS_PSLLW:
            dst_reg = INS_OperandReg(ins, OP_1);
            if(REG_is_xmm(dst_reg))
            {
                // Count operand is imm8
                if(INS_OperandIsImmediate(ins, OP_2))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftl_pw_xmm_imm_bits_2op128,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT64, INS_OperandImmediate(ins, OP_2),
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is XMM reg
                else if(INS_OperandIsReg(ins, OP_2))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftl_pw_xmm_xmm_bits_2op128,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT32, INS_OperandReg(ins, OP_2),
                        IARG_CONST_CONTEXT,
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is 128-bit memory location
                else
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftl_pw_xmm_m_bits_2op128,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_MEMORYREAD_EA,
                        IARG_UINT32, ins_indx,
                        IARG_END);
            }
            break;

        /* shift packed words right by count bits
         *      t[dst[0:15]] = t[dst[0:15]] << count
         * upper 128 bits unmodified for dst xmm register
         */
        case XED_ICLASS_PSRLW:
            dst_reg = INS_OperandReg(ins, OP_1);
            if(REG_is_xmm(dst_reg))
            {
                // Count operand is imm8
                if(INS_OperandIsImmediate(ins, OP_2))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftr_pw_xmm_imm_bits_2op128,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT64, INS_OperandImmediate(ins, OP_2),
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is XMM reg
                else if(INS_OperandIsReg(ins, OP_2))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftr_pw_xmm_xmm_bits_2op128,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT32, INS_OperandReg(ins, OP_2),
                        IARG_CONST_CONTEXT,
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is 128-bit memory location
                else
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftr_pw_xmm_m_bits_2op128,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_MEMORYREAD_EA,
                        IARG_UINT32, ins_indx,
                        IARG_END);
            }
            break;
        
        /* shift packed dwords left by count bits
         *      t[dst[0:31]] = t[dst[0:31]] << count
         * upper 128 bits of dst ymm register unmodified.
         */
        case XED_ICLASS_PSLLD:
            dst_reg = INS_OperandReg(ins, OP_1);
            if(REG_is_xmm(dst_reg))
            {
                // Count operand is imm8
                if(INS_OperandIsImmediate(ins, OP_2))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftl_pd_xmm_imm_bits_2op128,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT64, INS_OperandImmediate(ins, OP_2),
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is XMM reg
                else if(INS_OperandIsReg(ins, OP_2))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftl_pd_xmm_xmm_bits_2op128,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT32, INS_OperandReg(ins, OP_2),
                        IARG_CONST_CONTEXT,
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is 128-bit memory location
                else
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftl_pd_xmm_m_bits_2op128,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_MEMORYREAD_EA,
                        IARG_UINT32, ins_indx,
                        IARG_END);
            }
            break;
        
        /* shift packed dwords right by count bits
         *      t[dst[0:31]] = t[dst[0:31]] << count
         * upper 128 bits of dst ymm register unmodified.
         */
        case XED_ICLASS_PSRLD:
            dst_reg = INS_OperandReg(ins, OP_1);
            if(REG_is_xmm(dst_reg))
            {
                // Count operand is imm8
                if(INS_OperandIsImmediate(ins, OP_2))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftr_pd_xmm_imm_bits_2op128,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT64, INS_OperandImmediate(ins, OP_2),
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is XMM reg
                else if(INS_OperandIsReg(ins, OP_2))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftr_pd_xmm_xmm_bits_2op128,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT32, INS_OperandReg(ins, OP_2),
                        IARG_CONST_CONTEXT,
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is 128-bit memory location
                else
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftr_pd_xmm_m_bits_2op128,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_MEMORYREAD_EA,
                        IARG_UINT32, ins_indx,
                        IARG_END);
            }
            break;
        
        /* shift packed qwords left by count bits
         *      t[dst[0:63]] = t[dst[0:63]] << count
         * upper 128 bits of dst ymm register unmodified.
         */
        case XED_ICLASS_PSLLQ:
            dst_reg = INS_OperandReg(ins, OP_1);
            if(REG_is_xmm(dst_reg))
            {
                // Count operand is imm8
                if(INS_OperandIsImmediate(ins, OP_2))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftl_pq_xmm_imm_bits_2op128,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT64, INS_OperandImmediate(ins, OP_2),
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is XMM reg
                else if(INS_OperandIsReg(ins, OP_2))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftl_pq_xmm_xmm_bits_2op128,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT32, INS_OperandReg(ins, OP_2),
                        IARG_CONST_CONTEXT,
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is 128-bit memory location
                else
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftl_pq_xmm_m_bits_2op128,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_MEMORYREAD_EA,
                        IARG_UINT32, ins_indx,
                        IARG_END);
            }
            break;
        /* shift packed qwords right by count bits
         *      t[dst[0:63]] = t[dst[0:63]] << count
         * upper 128 bits of dst ymm register unmodified.
         */
        case XED_ICLASS_PSRLQ:
            dst_reg = INS_OperandReg(ins, OP_1);
            if(REG_is_xmm(dst_reg))
            {
                // Count operand is imm8
                if(INS_OperandIsImmediate(ins, OP_2))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftr_pq_xmm_imm_bits_2op128,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT64, INS_OperandImmediate(ins, OP_2),
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is XMM reg
                else if(INS_OperandIsReg(ins, OP_2))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftr_pq_xmm_xmm_bits_2op128,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT32, INS_OperandReg(ins, OP_2),
                        IARG_CONST_CONTEXT,
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is 128-bit memory location
                else
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftr_pq_xmm_m_bits_2op128,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_MEMORYREAD_EA,
                        IARG_UINT32, ins_indx,
                        IARG_END);
            }
            break;

        /* shift packed words left by count bits
         *      t[dst[0:15]] = t[dst[0:15]] << count
         * AVX version: upper 128 bits zeroed for dst xmm register
         */
        case XED_ICLASS_VPSLLW:
            dst_reg = INS_OperandReg(ins, OP_1);
            if(REG_is_xmm(dst_reg))
            {
                // Count operand is imm8
                if(INS_OperandIsImmediate(ins, OP_3))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftl_pw_xmm_imm_bits_3op128_zero_upper,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is XMM reg
                else if(INS_OperandIsReg(ins, OP_3))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftl_pw_xmm_xmm_bits_3op128_zero_upper,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT32, INS_OperandReg(ins, OP_3),
                        IARG_CONST_CONTEXT,
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is 128-bit memory location
                else
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftl_pw_xmm_m_bits_3op128_zero_upper,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_MEMORYREAD_EA,
                        IARG_UINT32, ins_indx,
                        IARG_END);
            }
            // YMM registers
            else
            {
                // Count operand is imm8
                if(INS_OperandIsImmediate(ins, OP_3))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftl_pw_ymm_imm_bits_3op256,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, YMM_INDX(dst_reg),
                        IARG_UINT32, YMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is XMM reg
                else if(INS_OperandIsReg(ins, OP_3))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftl_pw_ymm_ymm_bits_3op256,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, YMM_INDX(dst_reg),
                        IARG_UINT32, YMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT32, INS_OperandReg(ins, OP_3),
                        IARG_CONST_CONTEXT,
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is 256-bit memory location
                else
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftl_pw_ymm_m_bits_3op256,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, YMM_INDX(dst_reg),
                        IARG_UINT32, YMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_MEMORYREAD_EA,
                        IARG_UINT32, ins_indx,
                        IARG_END);
            }
            break;
        
        /* shift packed words right by count bits
         *      t[dst[0:15]] = t[dst[0:15]] >> count
         * AVX version: upper 128 bits zeroed for dst xmm register
         */
        case XED_ICLASS_VPSRLW:
            dst_reg = INS_OperandReg(ins, OP_1);
            if(REG_is_xmm(dst_reg))
            {
                // Count operand is imm8
                if(INS_OperandIsImmediate(ins, OP_3))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftr_pw_xmm_imm_bits_3op128_zero_upper,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is XMM reg
                else if(INS_OperandIsReg(ins, OP_3))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftr_pw_xmm_xmm_bits_3op128_zero_upper,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT32, INS_OperandReg(ins, OP_3),
                        IARG_CONST_CONTEXT,
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is 128-bit memory location
                else
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftr_pw_xmm_m_bits_3op128_zero_upper,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_MEMORYREAD_EA,
                        IARG_UINT32, ins_indx,
                        IARG_END);
            }
            // YMM registers
            else
            {
                // Count operand is imm8
                if(INS_OperandIsImmediate(ins, OP_3))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftr_pw_ymm_imm_bits_3op256,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, YMM_INDX(dst_reg),
                        IARG_UINT32, YMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is XMM reg
                else if(INS_OperandIsReg(ins, OP_3))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftr_pw_ymm_ymm_bits_3op256,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, YMM_INDX(dst_reg),
                        IARG_UINT32, YMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT32, INS_OperandReg(ins, OP_3),
                        IARG_CONST_CONTEXT,
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is 256-bit memory location
                else
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftr_pw_ymm_m_bits_3op256,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, YMM_INDX(dst_reg),
                        IARG_UINT32, YMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_MEMORYREAD_EA,
                        IARG_UINT32, ins_indx,
                        IARG_END);
            }
            break;

        /* shift packed dwords left by count bits
         *      t[dst[0:31]] = t[dst[0:31]] << count
         * AVX version: upper 128 bits zeroed for dst xmm register
         */
        case XED_ICLASS_VPSLLD:
            dst_reg = INS_OperandReg(ins, OP_1);
            if(REG_is_xmm(dst_reg))
            {
                // Count operand is imm8
                if(INS_OperandIsImmediate(ins, OP_3))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftl_pd_xmm_imm_bits_3op128_zero_upper,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is XMM reg
                else if(INS_OperandIsReg(ins, OP_3))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftl_pd_xmm_xmm_bits_3op128_zero_upper,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT32, INS_OperandReg(ins, OP_3),
                        IARG_CONST_CONTEXT,
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is 128-bit memory location
                else
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftl_pd_xmm_m_bits_3op128_zero_upper,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_MEMORYREAD_EA,
                        IARG_UINT32, ins_indx,
                        IARG_END);
            }
            // YMM registers
            else
            {
                // Count operand is imm8
                if(INS_OperandIsImmediate(ins, OP_3))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftl_pd_ymm_imm_bits_3op256,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, YMM_INDX(dst_reg),
                        IARG_UINT32, YMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is XMM reg
                else if(INS_OperandIsReg(ins, OP_3))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftl_pd_ymm_ymm_bits_3op256,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, YMM_INDX(dst_reg),
                        IARG_UINT32, YMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT32, INS_OperandReg(ins, OP_3),
                        IARG_CONST_CONTEXT,
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is 256-bit memory location
                else
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftl_pd_ymm_m_bits_3op256,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, YMM_INDX(dst_reg),
                        IARG_UINT32, YMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_MEMORYREAD_EA,
                        IARG_UINT32, ins_indx,
                        IARG_END);
            }
            break;
        
        /* shift packed dwords right by count bits
         *      t[dst[0:31]] = t[dst[0:31]] << count
         * AVX version: upper 128 bits zeroed for dst xmm register
         */
        case XED_ICLASS_VPSRLD:
            dst_reg = INS_OperandReg(ins, OP_1);
            if(REG_is_xmm(dst_reg))
            {
                // Count operand is imm8
                if(INS_OperandIsImmediate(ins, OP_3))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftr_pd_xmm_imm_bits_3op128_zero_upper,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is XMM reg
                else if(INS_OperandIsReg(ins, OP_3))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftr_pd_xmm_xmm_bits_3op128_zero_upper,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT32, INS_OperandReg(ins, OP_3),
                        IARG_CONST_CONTEXT,
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is 128-bit memory location
                else
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftr_pd_xmm_m_bits_3op128_zero_upper,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_MEMORYREAD_EA,
                        IARG_UINT32, ins_indx,
                        IARG_END);
            }
            // YMM registers
            else
            {
                // Count operand is imm8
                if(INS_OperandIsImmediate(ins, OP_3))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftr_pd_ymm_imm_bits_3op256,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, YMM_INDX(dst_reg),
                        IARG_UINT32, YMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is XMM reg
                else if(INS_OperandIsReg(ins, OP_3))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftr_pd_ymm_ymm_bits_3op256,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, YMM_INDX(dst_reg),
                        IARG_UINT32, YMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT32, INS_OperandReg(ins, OP_3),
                        IARG_CONST_CONTEXT,
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is 256-bit memory location
                else
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftr_pd_ymm_m_bits_3op256,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, YMM_INDX(dst_reg),
                        IARG_UINT32, YMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_MEMORYREAD_EA,
                        IARG_UINT32, ins_indx,
                        IARG_END);
            }
            break;

        /* shift packed qwords left by count bits
         *      t[dst[0:63]] = t[dst[0:63]] << count
         * AVX version: upper 128 bits zeroed for dst xmm register
         */
        case XED_ICLASS_VPSLLQ:
            dst_reg = INS_OperandReg(ins, OP_1);
            if(REG_is_xmm(dst_reg))
            {
                // Count operand is imm8
                if(INS_OperandIsImmediate(ins, OP_3))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftl_pq_xmm_imm_bits_3op128_zero_upper,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is XMM reg
                else if(INS_OperandIsReg(ins, OP_3))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftl_pq_xmm_xmm_bits_3op128_zero_upper,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT32, INS_OperandReg(ins, OP_3),
                        IARG_CONST_CONTEXT,
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is 128-bit memory location
                else
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftl_pq_xmm_m_bits_3op128_zero_upper,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_MEMORYREAD_EA,
                        IARG_UINT32, ins_indx,
                        IARG_END);
            }
            // YMM registers
            else
            {
                // Count operand is imm8
                if(INS_OperandIsImmediate(ins, OP_3))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftl_pq_ymm_imm_bits_3op256,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, YMM_INDX(dst_reg),
                        IARG_UINT32, YMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is XMM reg
                else if(INS_OperandIsReg(ins, OP_3))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftl_pq_ymm_ymm_bits_3op256,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, YMM_INDX(dst_reg),
                        IARG_UINT32, YMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT32, INS_OperandReg(ins, OP_3),
                        IARG_CONST_CONTEXT,
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is 256-bit memory location
                else
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftl_pq_ymm_m_bits_3op256,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, YMM_INDX(dst_reg),
                        IARG_UINT32, YMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_MEMORYREAD_EA,
                        IARG_UINT32, ins_indx,
                        IARG_END);
            }
            break;

        /* shift packed qwords right by count bits
         *      t[dst[0:63]] = t[dst[0:63]] << count
         * AVX version: upper 128 bits zeroed for dst xmm register
         */
        case XED_ICLASS_VPSRLQ:
            dst_reg = INS_OperandReg(ins, OP_1);
            if(REG_is_xmm(dst_reg))
            {
                // Count operand is imm8
                if(INS_OperandIsImmediate(ins, OP_3))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftr_pq_xmm_imm_bits_3op128_zero_upper,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is XMM reg
                else if(INS_OperandIsReg(ins, OP_3))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftr_pq_xmm_xmm_bits_3op128_zero_upper,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT32, INS_OperandReg(ins, OP_3),
                        IARG_CONST_CONTEXT,
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is 128-bit memory location
                else
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftr_pq_xmm_m_bits_3op128_zero_upper,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_MEMORYREAD_EA,
                        IARG_UINT32, ins_indx,
                        IARG_END);
            }
            // YMM registers
            else
            {
                // Count operand is imm8
                if(INS_OperandIsImmediate(ins, OP_3))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftr_pq_ymm_imm_bits_3op256,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, YMM_INDX(dst_reg),
                        IARG_UINT32, YMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is XMM reg
                else if(INS_OperandIsReg(ins, OP_3))
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftr_pq_ymm_ymm_bits_3op256,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, YMM_INDX(dst_reg),
                        IARG_UINT32, YMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT32, INS_OperandReg(ins, OP_3),
                        IARG_CONST_CONTEXT,
                        IARG_UINT32, ins_indx,
                        IARG_END);
                // Count operand is 256-bit memory location
                else
                    INS_InsertCall(ins, 
                        IPOINT_BEFORE,
                        (AFUNPTR) shiftr_pq_ymm_m_bits_3op256,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, YMM_INDX(dst_reg),
                        IARG_UINT32, YMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_MEMORYREAD_EA,
                        IARG_UINT32, ins_indx,
                        IARG_END);
            }
            break;

        /* Interleave low bytes of src and dst and stores
         * in dst operand. Taints likewise interleaved
         */
        case XED_ICLASS_PUNPCKLBW:
            dst_reg = INS_OperandReg(ins, OP_1);
            // Src is XMM reg
            if(INS_OperandIsReg(ins, OP_2))
                    INS_InsertCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR) interleave_low_b_xmm_xmm_2op128,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT32, ins_indx,
                        IARG_END);
            // Src is 128-bit memory location
            else
                    INS_InsertCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR) interleave_low_b_xmm_m_2op128,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_MEMORYREAD_EA,
                        IARG_UINT32, ins_indx,
                        IARG_END);
            break;

        /* Interleave low words of src and dst and stores
         * in dst operand. Taints likewise interleaved
         */
        case XED_ICLASS_PUNPCKLWD:
            dst_reg = INS_OperandReg(ins, OP_1);
            // Src is XMM reg
            if(INS_OperandIsReg(ins, OP_2))
                    INS_InsertCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR) interleave_low_w_xmm_xmm_2op128,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT32, ins_indx,
                        IARG_END);
            // Src is 128-bit memory location
            else
                    INS_InsertCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR) interleave_low_w_xmm_m_2op128,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_MEMORYREAD_EA,
                        IARG_UINT32, ins_indx,
                        IARG_END);
            break;

        case XED_ICLASS_RDRAND:
            dst_reg = INS_OperandReg(ins, OP_1);
            if(REG_is_gr16(dst_reg))
                    INS_InsertCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR) ins_clrw,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, REG16_INDX(dst_reg),
                        IARG_UINT32, ins_indx,
                        IARG_END);
            else
                    INS_InsertCall(ins,
                        IPOINT_BEFORE,
                        (AFUNPTR) ins_clrn,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, REG64_INDX(dst_reg),
                        IARG_UINT32, REG_Size(dst_reg),
                        IARG_UINT32, ins_indx,
                        IARG_END);
            break;

        /* Shift left count bits
         * t[dst] = t[dst] << count
         */
        case XED_ICLASS_SHL:
            // Register operand
            if(INS_OperandIsReg(ins, OP_1))
            {
                dst_reg = INS_OperandReg(ins, OP_1);
                // Count (second operand) is CL register
                if(INS_OperandIsReg(ins, OP_2))
                {
                    /* 64-bit operand */
                    if (REG_is_gr64(dst_reg))
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftl_r_bits_2op64,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_REG_VALUE, REG_CL,
                                //IARG_UINT32, REG8_INDX(REG_CL),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    /* 32-bit operand */
                    else if (REG_is_gr32(dst_reg))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftl_r_bits_2op32,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    /* 16-bit operand */
                    else if (REG_is_gr16(dst_reg))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftl_r_bits_2op16,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG16_INDX(dst_reg),
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    /* 8-bit operand (upper) */
                    else if (REG_is_Upper8(dst_reg))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftl_r_bits_2op8u,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    /* 8-bit operand (lower) */
                    else
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftl_r_bits_2op8l,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                }
                // Count (second operand) is immediate
                else if (INS_OperandIsImmediate(ins, OP_2))
                {
                    UINT64 imm = INS_OperandImmediate(ins, OP_2);
                    /* 64-bit operand */
                    if (REG_is_gr64(dst_reg))
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftl_r_bits_2op64,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT64, imm,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    /* 32-bit operand */
                    else if (REG_is_gr32(dst_reg))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftl_r_bits_2op32,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT64, imm,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    /* 16-bit operand */
                    else if (REG_is_gr16(dst_reg))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftl_r_bits_2op16,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG16_INDX(dst_reg),
                                IARG_UINT64, imm,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    /* 8-bit operand (upper) */
                    else if (REG_is_Upper8(dst_reg))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftl_r_bits_2op8u,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_UINT64, imm,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    /* 8-bit operand (lower) */
                    else
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftl_r_bits_2op8l,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_UINT64, imm,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                }
                else
                    printLog("Unhandled operand type\n");
                
            }
            // Dst operand is memory location
            else
            {
                // Count (second operand) is CL register
                if(INS_OperandIsReg(ins, OP_2))
                {
                    switch(INS_MemoryOperandSize(ins, OP_1))
                    {
                        /* 64-bit operand */
                        case BIT2BYTE(QWORD_BITS):
                            INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftl_m_bits_2op64,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                            break;
                        /* 32-bit operand */
                        case BIT2BYTE(DWORD_BITS):
                            INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftl_m_bits_2op32,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                            break;
                        /* 16-bit operand */
                        case BIT2BYTE(WORD_BITS):
                            INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftl_m_bits_2op16,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                            break;
                        /* 8-bit operand*/
                        case BIT2BYTE(BYTE_BITS):
                            INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftl_m_bits_2op8,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                            break;
                    }
                }
                // Count (second operand) is immediate
                else if (INS_OperandIsImmediate(ins, OP_2))
                {
                    UINT64 imm = INS_OperandImmediate(ins, OP_2);
                    switch(INS_MemoryOperandSize(ins, OP_1))
                    {
                        /* 64-bit operand */
                        case BIT2BYTE(QWORD_BITS):
                            INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftl_m_bits_2op64,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_UINT64, imm,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                            break;
                        /* 32-bit operand */
                        case BIT2BYTE(DWORD_BITS):
                            INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftl_m_bits_2op32,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_UINT64, imm,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                            break;
                    /* 16-bit operand */
                        case BIT2BYTE(WORD_BITS):
                            INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftl_m_bits_2op16,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_UINT64, imm,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                            break;
                        /* 8-bit operand */
                        case BIT2BYTE(BYTE_BITS):
                            INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftl_m_bits_2op8,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_UINT64, imm,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                            break;
                    }
                }
                else
                    printLog("Unhandled operand type\n");
                
            }
            break;
        
        /* Shift righ count bits
         * t[dst] = t[dst] << count
         */
        case XED_ICLASS_SAR:
        case XED_ICLASS_SHR:
            // Register operand
            if(INS_OperandIsReg(ins, OP_1))
            {
                dst_reg = INS_OperandReg(ins, OP_1);
                // Count (second operand) is CL register
                if(INS_OperandIsReg(ins, OP_2))
                {
                    /* 64-bit operand */
                    if (REG_is_gr64(dst_reg))
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftr_r_bits_2op64,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    /* 32-bit operand */
                    else if (REG_is_gr32(dst_reg))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftr_r_bits_2op32,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    /* 16-bit operand */
                    else if (REG_is_gr16(dst_reg))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftr_r_bits_2op16,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG16_INDX(dst_reg),
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    /* 8-bit operand (upper) */
                    else if (REG_is_Upper8(dst_reg))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftr_r_bits_2op8u,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    /* 8-bit operand (lower) */
                    else
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftr_r_bits_2op8l,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                }
                // Count (second operand) is immediate
                else if (INS_OperandIsImmediate(ins, OP_2))
                {
                    UINT64 imm = INS_OperandImmediate(ins, OP_2);
                    /* 64-bit operand */
                    if (REG_is_gr64(dst_reg))
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftr_r_bits_2op64,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT64, imm,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    /* 32-bit operand */
                    else if (REG_is_gr32(dst_reg))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftr_r_bits_2op32,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT64, imm,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    /* 16-bit operand */
                    else if (REG_is_gr16(dst_reg))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftr_r_bits_2op16,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG16_INDX(dst_reg),
                                IARG_UINT64, imm,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    /* 8-bit operand (upper) */
                    else if (REG_is_Upper8(dst_reg))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftr_r_bits_2op8u,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_UINT64, imm,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    /* 8-bit operand (lower) */
                    else
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftr_r_bits_2op8l,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_UINT64, imm,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                }
                else
                    printLog("Unhandled operand type\n");
                
            }
            // Dst operand is memory location
            else
            {
                // Count (second operand) is CL register
                if(INS_OperandIsReg(ins, OP_2))
                {
                    switch(INS_MemoryOperandSize(ins, OP_1))
                    {
                        /* 64-bit operand */
                        case BIT2BYTE(QWORD_BITS):
                            INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftr_m_bits_2op64,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                            break;
                        /* 32-bit operand */
                        case BIT2BYTE(DWORD_BITS):
                            INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftr_m_bits_2op32,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                            break;
                        /* 16-bit operand */
                        case BIT2BYTE(WORD_BITS):
                            INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftr_m_bits_2op16,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                            break;
                        /* 8-bit operand*/
                        case BIT2BYTE(BYTE_BITS):
                            INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftr_m_bits_2op8,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                            break;
                    }
                }
                // Count (second operand) is immediate
                else if (INS_OperandIsImmediate(ins, OP_2))
                {
                    UINT64 imm = INS_OperandImmediate(ins, OP_2);
                    switch(INS_MemoryOperandSize(ins, OP_1))
                    {
                        /* 64-bit operand */
                        case BIT2BYTE(QWORD_BITS):
                            INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftr_m_bits_2op64,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_UINT64, imm,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                            break;
                        /* 32-bit operand */
                        case BIT2BYTE(DWORD_BITS):
                            INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftr_m_bits_2op32,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_UINT64, imm,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                            break;
                    /* 16-bit operand */
                        case BIT2BYTE(WORD_BITS):
                            INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftr_m_bits_2op16,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_UINT64, imm,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                            break;
                        /* 8-bit operand */
                        case BIT2BYTE(BYTE_BITS):
                            INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftr_m_bits_2op8,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_UINT64, imm,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                            break;
                    }
                }
                else
                    printLog("Unhandled operand type\n");
                
            }
            break;

        /* shift 1st operand left count bits, shifting in bits from 
         * 2nd operand
         *      t[dst] = t[dst] << count | (t[src] >> (src_len - count)
         */
        case XED_ICLASS_SHLD: 
            // Both operands registers
            if(INS_OperandIsReg(ins, OP_1))
            {
                dst_reg = INS_OperandReg(ins, OP_1);
                src_reg = INS_OperandReg(ins, OP_2);
                //64-bit registers
                if(REG_is_gr64(src_reg))
                {
                    //count is immediate
                    if(INS_OperandIsImmediate(ins, OP_3))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftl_in_rr_bits_3op64,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT32, REG64_INDX(src_reg),
                                IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                                IARG_UINT32, INS_OperandWidth(ins, OP_2),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    // count is value in CL register
                    else
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftl_in_rr_bits_3op64,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT32, REG64_INDX(src_reg),
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, INS_OperandWidth(ins, OP_2),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                }
                //32-bit registers
                else if(REG_is_gr32(src_reg))
                {
                    //count is immediate
                    if(INS_OperandIsImmediate(ins, OP_3))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftl_in_rr_bits_3op32,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT32, REG64_INDX(src_reg),
                                IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                                IARG_UINT32, INS_OperandWidth(ins, OP_2),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    // count is value in CL register
                    else
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftl_in_rr_bits_3op32,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT32, REG64_INDX(src_reg),
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, INS_OperandWidth(ins, OP_2),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                }
                //16-bit registers
                else if(REG_is_gr16(src_reg))
                {
                    //count is immediate
                    if(INS_OperandIsImmediate(ins, OP_3))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftl_in_rr_bits_3op16,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG16_INDX(dst_reg),
                                IARG_UINT32, REG16_INDX(src_reg),
                                IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                                IARG_UINT32, INS_OperandWidth(ins, OP_2),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    // count is value in CL register
                    else
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftl_in_rr_bits_3op16,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG16_INDX(dst_reg),
                                IARG_UINT32, REG16_INDX(src_reg),
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, INS_OperandWidth(ins, OP_2),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                }
            }
            // Dst operand memory
            else
            {
                src_reg = INS_OperandReg(ins, OP_2);
                USIZE mem_len = INS_MemoryOperandSize(ins, OP_1);
                //64-bit
                if(mem_len == BIT2BYTE(QWORD_BITS))
                {
                    //count is immediate
                    if(INS_OperandIsImmediate(ins, OP_3))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftl_in_mr_bits_3op64,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_UINT32, REG64_INDX(src_reg),
                                IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                                IARG_UINT32, INS_OperandWidth(ins, OP_2),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    // count is value in CL register
                    else
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftl_in_mr_bits_3op64,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_UINT32, REG64_INDX(src_reg),
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, INS_OperandWidth(ins, OP_2),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                }
                // 32-bit 
                else if(mem_len == BIT2BYTE(DWORD_BITS))
                {
                    //count is immediate
                    if(INS_OperandIsImmediate(ins, OP_3))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftl_in_mr_bits_3op32,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_UINT32, REG64_INDX(src_reg),
                                IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                                IARG_UINT32, INS_OperandWidth(ins, OP_2),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    // count is value in CL register
                    else
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftl_in_mr_bits_3op32,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_UINT32, REG64_INDX(src_reg),
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, INS_OperandWidth(ins, OP_2),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                }
                // 16-bit
                else
                {
                    //count is immediate
                    if(INS_OperandIsImmediate(ins, OP_3))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftl_in_mr_bits_3op16,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_UINT32, REG16_INDX(src_reg),
                                IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                                IARG_UINT32, INS_OperandWidth(ins, OP_2),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    // count is value in CL register
                    else
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftl_in_mr_bits_3op16,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_UINT32, REG16_INDX(src_reg),
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, INS_OperandWidth(ins, OP_2),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                }
            }
            break;

        /* shift 1st operand right count bits, shifting in bits from 
         * 2nd operand
         *      t[dst] = t[dst] >> count | (t[src] << (src_len - count)
         */
        case XED_ICLASS_SHRD: 
            // Both operands registers
            if(INS_OperandIsReg(ins, OP_1))
            {
                dst_reg = INS_OperandReg(ins, OP_1);
                src_reg = INS_OperandReg(ins, OP_2);
                //64-bit registers
                if(REG_is_gr64(src_reg))
                {
                    //count is immediate
                    if(INS_OperandIsImmediate(ins, OP_3))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftr_in_rr_bits_3op64,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT32, REG64_INDX(src_reg),
                                IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                                IARG_UINT32, INS_OperandWidth(ins, OP_2),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    // count is value in CL register
                    else
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftr_in_rr_bits_3op64,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT32, REG64_INDX(src_reg),
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, INS_OperandWidth(ins, OP_2),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                }
                //32-bit registers
                else if(REG_is_gr32(src_reg))
                {
                    //count is immediate
                    if(INS_OperandIsImmediate(ins, OP_3))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftr_in_rr_bits_3op32,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT32, REG64_INDX(src_reg),
                                IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                                IARG_UINT32, INS_OperandWidth(ins, OP_2),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    // count is value in CL register
                    else
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftr_in_rr_bits_3op32,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT32, REG64_INDX(src_reg),
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, INS_OperandWidth(ins, OP_2),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                }
                //16-bit registers
                else if(REG_is_gr16(src_reg))
                {
                    //count is immediate
                    if(INS_OperandIsImmediate(ins, OP_3))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftr_in_rr_bits_3op16,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG16_INDX(dst_reg),
                                IARG_UINT32, REG16_INDX(src_reg),
                                IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                                IARG_UINT32, INS_OperandWidth(ins, OP_2),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    // count is value in CL register
                    else
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftr_in_rr_bits_3op16,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG16_INDX(dst_reg),
                                IARG_UINT32, REG16_INDX(src_reg),
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, INS_OperandWidth(ins, OP_2),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                }
            }
            // Dst operand memory
            else
            {
                src_reg = INS_OperandReg(ins, OP_2);
                USIZE mem_len = INS_MemoryOperandSize(ins, OP_1);
                //64-bit
                if(mem_len == BIT2BYTE(QWORD_BITS))
                {
                    //count is immediate
                    if(INS_OperandIsImmediate(ins, OP_3))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftr_in_mr_bits_3op64,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_UINT32, REG64_INDX(src_reg),
                                IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                                IARG_UINT32, INS_OperandWidth(ins, OP_2),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    // count is value in CL register
                    else
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftr_in_mr_bits_3op64,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_UINT32, REG64_INDX(src_reg),
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, INS_OperandWidth(ins, OP_2),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                }
                // 32-bit 
                else if(mem_len == BIT2BYTE(DWORD_BITS))
                {
                    //count is immediate
                    if(INS_OperandIsImmediate(ins, OP_3))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftr_in_mr_bits_3op32,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_UINT32, REG64_INDX(src_reg),
                                IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                                IARG_UINT32, INS_OperandWidth(ins, OP_2),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    // count is value in CL register
                    else
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftr_in_mr_bits_3op32,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_UINT32, REG64_INDX(src_reg),
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, INS_OperandWidth(ins, OP_2),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                }
                // 16-bit
                else
                {
                    //count is immediate
                    if(INS_OperandIsImmediate(ins, OP_3))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftr_in_mr_bits_3op16,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_UINT32, REG16_INDX(src_reg),
                                IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                                IARG_UINT32, INS_OperandWidth(ins, OP_2),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    // count is value in CL register
                    else
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)shiftr_in_mr_bits_3op16,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_UINT32, REG16_INDX(src_reg),
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, INS_OperandWidth(ins, OP_2),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                }
            }
            break;
        
        /* Shuffle byte instructions: shuffles the bytes of the dst
         * operand in place according to the indexes of the src operand, 
         * where the low 4 bits of each byte in the source operand are the 
         * index for the corresponding byte in the dst. If highest bit of 
         * the index byte is set, zero the byte.
         */
        case XED_ICLASS_PSHUFB:
            dst_reg = INS_OperandReg(ins, OP_1);
            if(REG_is_xmm(dst_reg))
            {
                // Source is reg
                if(INS_OperandIsReg(ins, OP_2))
                    INS_InsertCall(ins, 
                            IPOINT_BEFORE,
                            (AFUNPTR)shuf_b_xmm_xmm_2op128,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, XMM_INDX(dst_reg),
                            IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                            IARG_UINT32, INS_OperandReg(ins, OP_2),
                            IARG_CONST_CONTEXT,
                            IARG_UINT32, ins_indx,
                            IARG_END);
                // source is memory location
                else
                    printLog("pshufb unhandled operand: mem src\n");
                    
            }
            else
                printLog("pshufb unhandled operand: not xmm reg\n");
            break;
        case XED_ICLASS_VPSHUFB:
            dst_reg = INS_OperandReg(ins, OP_1);
            src1_reg = INS_OperandReg(ins, OP_2);
            if(REG_is_xmm(dst_reg))
            {
                // Source2 is reg
                if(INS_OperandIsReg(ins, OP_3))
                    INS_InsertCall(ins, 
                            IPOINT_BEFORE,
                            (AFUNPTR)shuf_b_xmm_xmm_3op128_zero_upper,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, XMM_INDX(dst_reg),
                            IARG_UINT32, XMM_INDX(src1_reg),
                            IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_3)),
                            IARG_UINT32, INS_OperandReg(ins, OP_3),
                            IARG_CONST_CONTEXT,
                            IARG_UINT32, ins_indx,
                            IARG_END);
                // source is memory location
                else
                    printLog("vpshufb unhandled operand: xmm mem src\n");
                    
            }
            else
                printLog("vpshufb unhandled operand: not xmm reg\n");
            break;

        /* shuffle dwords in src operand according to 2-bit order
         * values in third operand and save in dst operand.
         */
        case XED_ICLASS_PSHUFD:
            dst_reg = INS_OperandReg(ins, OP_1);
            if(REG_is_xmm(dst_reg))
            {
                // Source is reg
                if(INS_OperandIsReg(ins, OP_2))
                {
                    src_reg = INS_OperandReg(ins, OP_2);
                    INS_InsertCall(ins, 
                            IPOINT_BEFORE,
                            (AFUNPTR)shuf_dw_xmm_xmm_3op128,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, XMM_INDX(dst_reg),
                            IARG_UINT32, XMM_INDX(src_reg),
                            IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                            IARG_UINT32, ins_indx,
                            IARG_END);
                }
                // source is memory location
                else
                    printLog("pshufd unhandled operand: xmm mem src\n");
                    
            }
            else
                printLog("pshufd unhandled operand: not xmm reg\n");
            break;
        case XED_ICLASS_VPSHUFD:
            dst_reg = INS_OperandReg(ins, OP_1);
            if(REG_is_xmm(dst_reg))
            {
                // Source is reg
                if(INS_OperandIsReg(ins, OP_2))
                {
                    src_reg = INS_OperandReg(ins, OP_2);
                    INS_InsertCall(ins, 
                            IPOINT_BEFORE,
                            (AFUNPTR)shuf_dw_xmm_xmm_3op128_zero_upper,
                            IARG_REG_VALUE, thread_ctx_ptr,
                            IARG_UINT32, XMM_INDX(dst_reg),
                            IARG_UINT32, XMM_INDX(src_reg),
                            IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                            IARG_UINT32, ins_indx,
                            IARG_END);
                }
                // source is memory location
                else
                    printLog("vpshufd unhandled operand: xmm mem src\n");
                    
            }
            else
                printLog("vpshufd unhandled operand: not xmm reg\n");
            break;
        
        /* zero the upper 128 bits of all YMM registers*/
        case XED_ICLASS_VZEROUPPER:
                INS_InsertPredicatedCall(
                        ins, IPOINT_BEFORE, 
                        (AFUNPTR)handle_vzeroupper,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, ins_indx,
                        IARG_END);
            break;

        /* bswap: swap the byte order of the operand */
        case XED_ICLASS_BSWAP:
                INS_InsertCall(
                        ins, IPOINT_BEFORE, 
                        (AFUNPTR)bswap,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, REG64_INDX(INS_OperandReg(ins, OP_1)),
                        IARG_UINT32, INS_OperandWidth(ins, OP_1),
                        IARG_UINT32, ins_indx,
                        IARG_END);

            break;

    /*pcmpisitri: compares packed strings based on value in immediate
     * operand to generate an index and stores in ECX. 
     * Conservatively tainting ECX with union of all bytes in both source
     * operands
     * TODO: fix me?
     */
    case XED_ICLASS_PCMPISTRI:
        // Both xmm register operands
        if(INS_OperandIsReg(ins, OP_2))
                INS_InsertCall(
                        ins, IPOINT_BEFORE, 
                        (AFUNPTR) handle_pcmpistri_xmm,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_1)),
                        IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT32, ins_indx,
                        IARG_END);
        // dst is xmm reg, src operand is memory location
        else
                INS_InsertCall(
                        ins, IPOINT_BEFORE, 
                        (AFUNPTR) handle_pcmpistri_m,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_1)),
                        IARG_MEMORYREAD_EA,
                        IARG_UINT32, ins_indx,
                        IARG_END);
        break;
        

    //test if actually touch tainted data
    case XED_ICLASS_ROL:
    case XED_ICLASS_ROR:
            // Register operand
            if(INS_OperandIsReg(ins, OP_1))
            {
                dst_reg = INS_OperandReg(ins, OP_1);
                // Count (second operand) is CL register
                if(INS_OperandIsReg(ins, OP_2))
                {
                    /* 64-bit operand */
                    if (REG_is_gr64(dst_reg))
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)rotatel_r_bits_2op64,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, REG8_INDX(REG_CL),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    /* 32-bit operand */
                    else if (REG_is_gr32(dst_reg))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)rotatel_r_bits_2op32,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, REG8_INDX(REG_CL),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    /* 16-bit operand */
                    else if (REG_is_gr16(dst_reg))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)rotatel_r_bits_2op16,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG16_INDX(dst_reg),
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, REG8_INDX(REG_CL),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    /* 8-bit operand (upper) */
                    else if (REG_is_Upper8(dst_reg))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)rotatel_r_bits_2op8u,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, REG8_INDX(REG_CL),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    /* 8-bit operand (lower) */
                    else
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)rotatel_r_bits_2op8l,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, REG8_INDX(REG_CL),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                }
                // Count (second operand) is immediate
                else if (INS_OperandIsImmediate(ins, OP_2))
                {
                    UINT64 imm = INS_OperandImmediate(ins, OP_2);
                    /* 64-bit operand */
                    if (REG_is_gr64(dst_reg))
                        /* propagate the tag accordingly */
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)rotatel_r_bits_2op64,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT64, imm,
                                IARG_UINT32, 0,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    /* 32-bit operand */
                    else if (REG_is_gr32(dst_reg))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)rotatel_r_bits_2op32,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG64_INDX(dst_reg),
                                IARG_UINT64, imm,
                                IARG_UINT32, 0,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    /* 16-bit operand */
                    else if (REG_is_gr16(dst_reg))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)rotatel_r_bits_2op16,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG16_INDX(dst_reg),
                                IARG_UINT64, imm,
                                IARG_UINT32, 0,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    /* 8-bit operand (upper) */
                    else if (REG_is_Upper8(dst_reg))
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)rotatel_r_bits_2op8u,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_UINT64, imm,
                                IARG_UINT32, 0,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                    /* 8-bit operand (lower) */
                    else
                        INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)rotatel_r_bits_2op8l,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_UINT32, REG8_INDX(dst_reg),
                                IARG_UINT64, imm,
                                IARG_UINT32, 0,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                }
                else
                    printLog("Unhandled operand type\n");
                
            }
            // Dst operand is memory location
            else
            {
                // Count (second operand) is CL register
                if(INS_OperandIsReg(ins, OP_2))
                {
                    switch(INS_MemoryOperandSize(ins, OP_1))
                    {
                        /* 64-bit operand */
                        case BIT2BYTE(QWORD_BITS):
                            INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)rotatel_m_bits_2op64,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, REG8_INDX(REG_CL),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                            break;
                        /* 32-bit operand */
                        case BIT2BYTE(DWORD_BITS):
                            INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)rotatel_m_bits_2op32,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, REG8_INDX(REG_CL),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                            break;
                        /* 16-bit operand */
                        case BIT2BYTE(WORD_BITS):
                            INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)rotatel_m_bits_2op16,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, REG8_INDX(REG_CL),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                            break;
                        /* 8-bit operand*/
                        case BIT2BYTE(BYTE_BITS):
                            INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)rotatel_m_bits_2op8,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_REG_VALUE, REG_CL,
                                IARG_UINT32, REG8_INDX(REG_CL),
                                IARG_UINT32, ins_indx,
                                IARG_END);
                            break;
                    }
                }
                // Count (second operand) is immediate
                else if (INS_OperandIsImmediate(ins, OP_2))
                {
                    UINT64 imm = INS_OperandImmediate(ins, OP_2);
                    switch(INS_MemoryOperandSize(ins, OP_1))
                    {
                        /* 64-bit operand */
                        case BIT2BYTE(QWORD_BITS):
                            INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)rotatel_m_bits_2op64,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_UINT64, imm,
                                IARG_UINT32, 0,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                            break;
                        /* 32-bit operand */
                        case BIT2BYTE(DWORD_BITS):
                            INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)rotatel_m_bits_2op32,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_UINT64, imm,
                                IARG_UINT32, 0,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                            break;
                    /* 16-bit operand */
                        case BIT2BYTE(WORD_BITS):
                            INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)rotatel_m_bits_2op16,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_UINT64, imm,
                                IARG_UINT32, 0,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                            break;
                        /* 8-bit operand */
                        case BIT2BYTE(BYTE_BITS):
                            INS_InsertCall(ins,
                                IPOINT_BEFORE,
                                (AFUNPTR)rotatel_m_bits_2op8,
                                IARG_REG_VALUE, thread_ctx_ptr,
                                IARG_MEMORYREAD_EA,
                                IARG_UINT64, imm,
                                IARG_UINT32, 0,
                                IARG_UINT32, ins_indx,
                                IARG_END);
                            break;
                    }
                }
                else
                    printLog("Unhandled operand type\n");
                
            }
            break;

    case XED_ICLASS_PALIGNR:
            dst_reg = INS_OperandReg(ins, OP_1);
            if(INS_OperandIsReg(ins, OP_2))
                INS_InsertCall(
                    ins, IPOINT_BEFORE, 
                    (AFUNPTR)alignr_xmm_2op128,
                    IARG_REG_VALUE, thread_ctx_ptr,
                    IARG_UINT32, XMM_INDX(dst_reg),
                    IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                    IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                    IARG_UINT32, ins_indx,
                    IARG_END);
            else
                INS_InsertCall(
                    ins, IPOINT_BEFORE, 
                    (AFUNPTR)alignr_m_2op128,
                    IARG_REG_VALUE, thread_ctx_ptr,
                    IARG_UINT32, XMM_INDX(dst_reg),
                    IARG_MEMORYREAD_EA,
                    IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                    IARG_UINT32, ins_indx,
                    IARG_END);
            break;
    case XED_ICLASS_VPALIGNR:
            dst_reg = INS_OperandReg(ins, OP_1);
            if(REG_is_xmm(dst_reg))
            {
                if(INS_OperandIsReg(ins, OP_3))
                    INS_InsertCall(
                    ins, IPOINT_BEFORE, 
                    (AFUNPTR)alignr_xmm_xmm_3op128,
                    IARG_REG_VALUE, thread_ctx_ptr,
                    IARG_UINT32, XMM_INDX(dst_reg),
                    IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                    IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_3)),
                    IARG_UINT64, INS_OperandImmediate(ins, OP_4),
                    IARG_UINT32, ins_indx,
                    IARG_END);
                else
                    INS_InsertCall(
                    ins, IPOINT_BEFORE, 
                    (AFUNPTR)alignr_xmm_m_3op128,
                    IARG_REG_VALUE, thread_ctx_ptr,
                    IARG_UINT32, XMM_INDX(dst_reg),
                    IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                    IARG_MEMORYREAD_EA,
                    IARG_UINT64, INS_OperandImmediate(ins, OP_4),
                    IARG_UINT32, ins_indx,
                    IARG_END);
            }
            else
            {
                if(INS_OperandIsReg(ins, OP_3))
                    INS_InsertCall(
                    ins, IPOINT_BEFORE, 
                    (AFUNPTR)alignr_ymm_ymm_3op256,
                    IARG_REG_VALUE, thread_ctx_ptr,
                    IARG_UINT32, YMM_INDX(dst_reg),
                    IARG_UINT32, YMM_INDX(INS_OperandReg(ins, OP_2)),
                    IARG_UINT32, YMM_INDX(INS_OperandReg(ins, OP_3)),
                    IARG_UINT64, INS_OperandImmediate(ins, OP_4),
                    IARG_UINT32, ins_indx,
                    IARG_END);
                else
                    INS_InsertCall(
                    ins, IPOINT_BEFORE, 
                    (AFUNPTR)alignr_ymm_m_3op256,
                    IARG_REG_VALUE, thread_ctx_ptr,
                    IARG_UINT32, YMM_INDX(dst_reg),
                    IARG_UINT32, YMM_INDX(INS_OperandReg(ins, OP_2)),
                    IARG_MEMORYREAD_EA,
                    IARG_UINT64, INS_OperandImmediate(ins, OP_4),
                    IARG_UINT32, ins_indx,
                    IARG_END);
            }
            break;

    
    case XED_ICLASS_CVTSI2SD:
            dst_reg = INS_OperandReg(ins, OP_1);
            // both operands registers
            if(INS_OperandIsReg(ins, OP_2))
                INS_InsertCall(
                        ins, IPOINT_BEFORE, 
                        (AFUNPTR)cvtsi2sd_r2xmm,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT32, REG64_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT32, ins_indx,
                        IARG_END);
            // src 32-bit memory src
            else if (INS_OperandWidth(ins, OP_2) == DWORD_BITS)
                INS_InsertCall(
                        ins, IPOINT_BEFORE, 
                        (AFUNPTR)cvtsi2sd_m32_2xmm,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_MEMORYREAD_EA,
                        IARG_UINT32, ins_indx,
                        IARG_END);
            // src is 64-bit memory
            else
                INS_InsertCall(
                        ins, IPOINT_BEFORE, 
                        (AFUNPTR)cvtsi2sd_m64_2xmm,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_MEMORYREAD_EA,
                        IARG_UINT32, ins_indx,
                        IARG_END);
            break;
    /* Multiplies qwords from dst and src operand selected by bits 0 and 4
     * of the immediate byte
     */
    case XED_ICLASS_PCLMULQDQ:
        dst_reg = INS_OperandReg(ins, OP_1);
        //both operands xmm registers
        if(INS_OperandIsReg(ins, OP_2))
            INS_InsertCall(
                        ins, IPOINT_BEFORE, 
                        (AFUNPTR)pmulqdq_xmm_2op128,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT32, XMM_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                        IARG_UINT32, ins_indx,
                        IARG_END);
        // src operand memory location
        else
            INS_InsertCall(
                        ins, IPOINT_BEFORE, 
                        (AFUNPTR)pmulqdq_m_2op128,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_MEMORYREAD_EA,
                        IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                        IARG_UINT32, ins_indx,
                        IARG_END);
        break;

    case XED_ICLASS_PINSRD:
        dst_reg = INS_OperandReg(ins, OP_1);
        //both operands xmm registers
        if(INS_OperandIsReg(ins, OP_2))
            INS_InsertCall(
                        ins, IPOINT_BEFORE, 
                        (AFUNPTR)pinsrd_r_2op128,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_UINT32, REG64_INDX(INS_OperandReg(ins, OP_2)),
                        IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                        IARG_UINT32, ins_indx,
                        IARG_END);
        // src operand memory location
        else
            INS_InsertCall(
                        ins, IPOINT_BEFORE, 
                        (AFUNPTR)pinsrd_m_2op128,
                        IARG_REG_VALUE, thread_ctx_ptr,
                        IARG_UINT32, XMM_INDX(dst_reg),
                        IARG_MEMORYREAD_EA,
                        IARG_UINT64, INS_OperandImmediate(ins, OP_3),
                        IARG_UINT32, ins_indx,
                        IARG_END);
        break;


#if 0
        case XED_ICLASS_ENTER:
            printLog("unhandled opcode %s\n", OPCODE_StringShort(ins_indx));
            bREAK;
#endif
            
            /* 
             * default handler
             */
        default:
            /* iterator */
#ifdef TRACK_UNHANDLED_MEM_READS
            if(INS_IsMemoryRead(ins))
                INS_InsertPredicatedCall(
                        ins, IPOINT_BEFORE, 
                        (AFUNPTR)unhandled_mem_read,
                        IARG_MEMORYREAD_EA,
                        IARG_MEMORYREAD_SIZE,
                        IARG_UINT32, ins_indx,
                        IARG_END);
#endif
#ifdef TRACK_UNHANDLED_INS
            if (unhandled_ins_set.find(ins_indx) == unhandled_ins_set.end())
            {
                unhandled_ins_set.insert(ins_indx);
                (void)fprintf(stdout, "instruction not handled: %s: %s\n",
                        OPCODE_StringShort(ins_indx).c_str(), 
                        INS_Disassemble(ins).c_str()); 
            }
#endif
            break;
    }
//    if(instrumentFlag)
//        CODECACHE_FlushCache();
}
