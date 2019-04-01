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
#include <stdarg.h>
#include <sstream>

#include "pin.H"
#include "libdft_api.h"
#include "libdft_instrument.h"
#include "libdft_analysis.h"
#include "tagmap.h"
#include "branch_pred.h"

static unsigned int  declassify_length;

/* thread context */
extern REG	thread_ctx_ptr;


// For special ins injection mode to declassify/debug, store memory length
int mem_len = 0;

// pretty printing constants
enum position{
    PRE,
    POST
};
enum op_types{
    GPR8,
    GPR8H,
    GPR16,
    GPR32,
    GPR64,
    XMM,
    YMM,
    ZMM,
    M8,
    M16,
    M32,
    M64,
    M128,
    M256,
    M512
};


//static functions -- copied here for performance

/* Returns the address of the taint tag corresponding to the virtual
 * addr
 */
static ADDRINT get_tag_address(ADDRINT vaddr)
{
    // Kernel pages all map to same tag
    if(unlikely(IN_KERNEL_SPACE(vaddr)))
    {
#ifdef TAGMAP_DEBUG
        printLog("kernel mem access: %p -> %p\n", vaddr, KERNEL_TAINT_PAGE);
#endif
        return KERNEL_TAINT_PAGE;
    }

    tagmap_l2_t l2 = (tagmap_l2_t)TAGMAP_L1[L1_INDX_BITS(vaddr)];
#ifdef DEBUG 
    //printLog("getting tag for vaddr %p: [%x][%x]\n", vaddr,
    //        L1_INDX_BITS(vaddr), L2_INDX_BITS(vaddr));
    if(!l2)
    {

        printLog("TAGMAP ERROR for vaddr %p: l1 indx 0x%x is NULL\n", 
			vaddr, L1_INDX_BITS(vaddr));
        return KERNEL_TAINT_PAGE;
    }
    
    if(!l2[L2_INDX_BITS(vaddr)])
    {

        printLog("TAGMAP ERROR for vaddr %p: l2 indx 0x%x is NULL\n", 
			vaddr, L2_INDX_BITS(vaddr));
        return KERNEL_TAINT_PAGE;
    }
#endif
    ADDRINT tagaddr = vaddr + l2[L2_INDX_BITS(vaddr)];
    //printLog("offset is 0x%lx. Tag addr is 0x%lx\n", l2[L2_INDX_BITS(vaddr)], tagaddr);
    return tagaddr;
}

/* Copy taint from 32-bit memory location to 32-bit register
 * Upper 32-bits of the register are cleared, so clear the 
 * associated tag bits.
 */
static inline void m2r_mov_32(thread_ctx_t *thread_ctx, 
        UINT32 dst_reg, ADDRINT src)
{
	*((UINT32 *)&thread_ctx->vcpu.gpr[dst_reg]) =
		*((UINT32 *)get_tag_address(src));

    // upper 32 bits of register are cleared withe a 32-bit operarand so
    // clear the tags
	*((UINT32 *)&thread_ctx->vcpu.gpr[dst_reg] + 1) = TAG_ZERO;
}

/* Union taint from 32-bit memory location with 32-bit register
 * Upper 32-bits of the register are cleared, so clear the 
 * associated tag bits.
 */
static inline void m2r_union_32(thread_ctx_t *thread_ctx, 
        UINT32 dst_reg, ADDRINT src)
{
	*((UINT32 *)&thread_ctx->vcpu.gpr[dst_reg]) |=
		*((UINT32 *)get_tag_address(src));

    // upper 32 bits of register are cleared withe a 32-bit operarand so
    // clear the tags
	*((UINT32 *)&thread_ctx->vcpu.gpr[dst_reg] + 1) = TAG_ZERO;
}
#if 0
/*
 * tag propagation (analysis function)
 *
 * extend the tag as follows: t[upper(eax)] = t[ax]
 *
 * NOTE: special case for the CWDE instruction
 *
 * @thread_ctx:	the thread context
 */
 void PIN_FAST_ANALYSIS_CALL
_cwde(thread_ctx_t *thread_ctx)
{
	*(((uint16_t *)&thread_ctx->vcpu.gpr[7]) + 1) =
		*((uint16_t *)&thread_ctx->vcpu.gpr[7]);
}
#endif

void pretty_print_taint(thread_ctx_t *thread_ctx, UINT32 opcode, int tainted, 
        int num_ops, int position, ...)
{
    //printLog("%s\n",OPCODE_StringShort(opcode).c_str());
    //return;
//}
#if 1
    va_list valist;
    int i;
    stringstream ss;

    // check for pre/postprop flag and tainted
    if(tainted)
    {

        va_start(valist, position);
        string pos = (position == POST) ? "POST":"PRE";
        ss << pos << " " <<   OPCODE_StringShort(opcode);
        ADDRINT addr;
        UINT32 reg_num;

        //extract from all operands the op type and the op, 
        //and add to output string
        for (i = 0; i < num_ops; i++) 
        {
            switch(i)
            {
                case 0:
                    ss << "\n    dst ";
                    break;
                case 1:
                    ss << "\n    src1 ";
                    break;
                case 2:
                    ss << "\n    src2 ";
                    break;
                default:
                    ss <<  "\n    extra ";
                    break;
            }

            switch(va_arg(valist, int))
            {
                case GPR8:
                    reg_num = va_arg(valist, UINT32);
                    ss <<  string("gpr8 ") << reg_num << string(" taint: ") << 
                        hexstr(*(((uint8_t *)&thread_ctx->vcpu.gpr[reg_num])));
                    break;
                case GPR8H:
                    reg_num = va_arg(valist, UINT32);
                    ss <<  string("gpr8H ") << reg_num << string(" taint: ") << 
                        hexstr(*(((uint8_t *)&thread_ctx->vcpu.gpr[reg_num]) + 1));
                    break;
                case GPR16:
                    reg_num = va_arg(valist, UINT32);
                    ss <<  string("gpr16 ") << reg_num << " taint: " << 
                        hexstr(*(((uint16_t *)&thread_ctx->vcpu.gpr[reg_num])));
                    break;
                case GPR32:
                    reg_num = va_arg(valist, UINT32);
                    ss << "gpr32 " << reg_num << " taint: " << 
                        hexstr(*(((uint32_t *)&thread_ctx->vcpu.gpr[reg_num])));
                    break;
                case GPR64:
                    reg_num = va_arg(valist, UINT32);
                    ss << "gpr64 " << reg_num << " taint: " << 
                        hexstr(*(((uint64_t *)&thread_ctx->vcpu.gpr[reg_num])));
                    break;
                case XMM:
                    reg_num = va_arg(valist, UINT32);
                    ss << "xmm " << reg_num << " taint: " << 
                        uint128_hex_string(&thread_ctx->vcpu.avx[reg_num][0]).c_str();
                    break;
                case YMM:
                    reg_num = va_arg(valist, UINT32);
                    ss << "ymm " << reg_num << " taint: " << 
                        uint256_hex_string(&thread_ctx->vcpu.avx[reg_num]).c_str();
                    break;
                case M8:
                    addr = va_arg(valist, ADDRINT);
                    ss << "mem8 " << hexstr(addr) << " taint: " << 
                        hexstr(*(uint8_t *)get_tag_address(addr));
                    break;
                case M16:
                    addr = va_arg(valist, ADDRINT);
                    ss << "mem16 " << hexstr(addr) << " taint: " << 
                        hexstr(*(uint16_t *)get_tag_address(addr));
                    break;
                case M32:
                    addr = va_arg(valist, ADDRINT);
                    ss << "mem32 " << hexstr(addr) << " taint: " << 
                        hexstr(*(uint32_t *)get_tag_address(addr));
                    break;
                case M64:
                    addr = va_arg(valist, ADDRINT);
                    ss << "mem64 " << hexstr(addr) << " taint: " << 
                        hexstr(*(uint64_t *)get_tag_address(addr));
                    break;
                case M128:
                    addr = va_arg(valist, ADDRINT);
                    ss << "mem128 " << hexstr(addr) << " taint: " << 
                        uint128_hex_string((uint128_t *)get_tag_address(addr)).c_str();
                    break;
                case M256:
                    addr = va_arg(valist, ADDRINT);
                    ss << "mem256 " << hexstr(addr) << " taint: " << 
                        uint256_hex_string((uint256_t *)get_tag_address(addr)).c_str();
                    break;
                case M512:
                    addr = va_arg(valist, ADDRINT);
                    ss << "mem512 " << hexstr(addr) << " taint: " << 
                        uint512_hex_string((uint512_t *)get_tag_address(addr)).c_str();
                    break;
            }
        }

        /* clean memory reserved for valist */
        va_end(valist); 

        ss << "\n";
        printLog(ss.str().c_str());
    }
}
#endif
        
/*
 * untag a byte in the virtual address space
 *
 * @addr:	the virtual address
 */
void PIN_FAST_ANALYSIS_CALL
ins_clrb(ADDRINT addr, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(uint8_t *)(get_tag_address(addr)))
        tainted = 1;
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %p- taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                addr, *(uint8_t *)(get_tag_address(addr)));
#endif
    /* clear the byte that corresponds to the given address */
	*(uint8_t *)(get_tag_address(addr)) = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: cleared 1 byte at: %p- taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                addr, *(uint8_t *)(get_tag_address(addr)));
#endif
}

/*
 * untag a word (i.e., 2 bytes) in the virtual address space
 *
 * @addr:	the virtual address
 */
void PIN_FAST_ANALYSIS_CALL
ins_clrw(ADDRINT addr, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(uint16_t *)(get_tag_address(addr)))
        tainted = 1;
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %p- taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                addr, *(uint16_t *)(get_tag_address(addr)));
#endif
	/* clear the bytes that correspond to the addresses of the word */
	*(uint16_t *)(get_tag_address(addr)) = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: cleared 2 bytes at %p- taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                addr, *(uint16_t *)(get_tag_address(addr)));
#endif
}

/*
 * untag a long word (i.e., 4 bytes) in the virtual address space
 *
 * @addr:	the virtual address
 */
void PIN_FAST_ANALYSIS_CALL
ins_clrl(ADDRINT addr, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(uint32_t *)(get_tag_address(addr)))
        tainted = 1;
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %p- taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                addr, *(uint32_t *)(get_tag_address(addr)));
#endif
	/* clear the bytes that correspond to the addresses of the long word */
	*(uint32_t *)(get_tag_address(addr)) = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted){
        printLog("Post %s: cleared 4 bytes at %p- taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                addr, *(uint32_t *)(get_tag_address(addr)));
    }
#endif
}

/*
 * untag a long word (i.e., 4 bytes) in the virtual address space
 *
 * @addr:	the virtual address
 */
void PIN_FAST_ANALYSIS_CALL
ins_clrn(ADDRINT addr, UINT32 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(mem_is_tainted(addr, count))
        tainted = 1;
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %p- taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                addr, mem_is_tainted(addr, count));
#endif
    memset((void *)addr, TAG_ZERO, count);

#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted){
        printLog("Post %s: cleared 4 bytes at %p- taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                addr, mem_is_tainted(addr, count));
    }
#endif
}

/*
 * untag a long long word (i.e., 8 bytes) in the virtual address space
 *
 * @addr:	the virtual address
 */
void PIN_FAST_ANALYSIS_CALL
ins_clrll(ADDRINT addr, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(ADDRINT *)(get_tag_address(addr)))
        tainted = 1;
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %p- taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                addr, *(ADDRINT *)(get_tag_address(addr)));
#endif
	/* clear the bytes that correspond to the addresses of the long word */
	*(ADDRINT *)(get_tag_address(addr)) = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted){
        printLog("Post %s: cleared 4 bytes at %p- taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                addr, *(ADDRINT *)(get_tag_address(addr)));
    }
#endif
}


/*
 * tag propagation (analysis function)
 *
 * propagate and extend tag from an upper 8-bit register
 * to a 16-bit register t[dst] = t[upper(src)]
 *
 * NOTE: special case for MOVSX instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
void PIN_FAST_ANALYSIS_CALL
sx_r2r_opwb_u(thread_ctx_t *thread_ctx, UINT32 dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1) || *(((uint16_t *)&thread_ctx->vcpu.gpr[dst])))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
    tainted=1;
#endif
#endif

    /* temporary tag value */
	uint8_t src_tag = *(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1);

	/* update the destination (xfer) */
	*((uint8_t *)&thread_ctx->vcpu.gpr[dst])	= src_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 1)	= src_tag;

#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 2, POST, GPR16, dst, GPR8H, src);
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate and extend tag from a lower 8-bit register  
 * to a 16-bit register as t[dst] = t[lower(src)]
 *
 * NOTE: special case for MOVSX instruction
 *and CBW
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
sx_r2r_opwb_l(thread_ctx_t *thread_ctx, UINT32 dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint8_t *)&thread_ctx->vcpu.gpr[src])) || *(((uint16_t *)&thread_ctx->vcpu.gpr[dst])))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
#endif
	/* temporary tag value */
	uint8_t src_tag = *((uint8_t *)&thread_ctx->vcpu.gpr[src]);

	/* update the destination (xfer) */
	*((uint8_t *)&thread_ctx->vcpu.gpr[dst])	= src_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 1)	= src_tag;

#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 2, POST, GPR16, dst, GPR8, src);
#endif
}


/*
 * tag propagation (analysis function)
 *
 * propagate and extend tag between from an upper 8-bit register
 * to a 64-bit register as t[dst] = t[upper(src)]
 *
 * NOTE: special case for MOVSX instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
sx_r2r_opqwb_u(thread_ctx_t *thread_ctx, UINT32 dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1) || 
            thread_ctx->vcpu.gpr[dst])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
#endif
	/* temporary tag value */
	uint8_t src_tag = *(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1);

	/* update the destination (xfer) */
	*((uint8_t *)&thread_ctx->vcpu.gpr[dst])	= src_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 1)	= src_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 2)	= src_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 3)	= src_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 4)	= src_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 5)	= src_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 6)	= src_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 7)	= src_tag;

#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 2, POST, GPR64, dst, GPR8H, src);
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate and extend tag from a lower 8-bit regester
 * to a 64 bit regiester as t[dst] = t[lower(src)]
 *
 * NOTE: special case for MOVSX instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
sx_r2r_opqwb_l(thread_ctx_t *thread_ctx, UINT32 dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint8_t *)&thread_ctx->vcpu.gpr[src])) || 
            thread_ctx->vcpu.gpr[dst])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
#endif
	/* temporary tag value */
	uint8_t src_tag = *((uint8_t *)&thread_ctx->vcpu.gpr[src]);

	/* update the destination (xfer) */
	*((uint8_t *)&thread_ctx->vcpu.gpr[dst])	= src_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 1)	= src_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 2)	= src_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 3)	= src_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 4)	= src_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 5)	= src_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 6)	= src_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 7)	= src_tag;
#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 2, POST, GPR64, dst, GPR8, src);
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate and extend tag from a 16-bit register 
 * to a 64-bit register as t[dst] = t[src]
 *
 * NOTE: special case for MOVSX instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
sx_r2r_opqww(thread_ctx_t *thread_ctx, UINT32 dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint16_t *)&thread_ctx->vcpu.gpr[src])) || 
            thread_ctx->vcpu.gpr[dst])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
#endif
	/* temporary tag value */
	uint16_t src_tag = *((uint16_t *)&thread_ctx->vcpu.gpr[src]);

	/* update the destination (xfer) */
	*((uint16_t *)&thread_ctx->vcpu.gpr[dst])	= src_tag;
	*(((uint16_t *)&thread_ctx->vcpu.gpr[dst]) + 1)	= src_tag;
	*(((uint16_t *)&thread_ctx->vcpu.gpr[dst]) + 2)	= src_tag;
	*(((uint16_t *)&thread_ctx->vcpu.gpr[dst]) + 3)	= src_tag;
    
    
#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 2, POST, GPR64, dst, GPR16, src);
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate and extend tag between from an upper 8-bit register
 * to a 32-bit register as t[dst] = t[upper(src)]
 *
 * NOTE: special case for MOVSX instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
sx_r2r_oplb_u(thread_ctx_t *thread_ctx, UINT32 dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1) || 
            *(((UINT32 *)&thread_ctx->vcpu.gpr[dst])))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
#endif
	/* temporary tag value */
	uint8_t src_tag = *(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1);

	/* update the destination (xfer) */
	*((uint8_t *)&thread_ctx->vcpu.gpr[dst])	= src_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 1)	= src_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 2)	= src_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 3)	= src_tag;
#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 2, POST, GPR32, dst, GPR8H, src);
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate and extend tag from a lower 8-bit regester
 * to a 32 bit regiester as t[dst] = t[lower(src)]
 *
 * NOTE: special case for MOVSX instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
sx_r2r_oplb_l(thread_ctx_t *thread_ctx, UINT32 dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint8_t *)&thread_ctx->vcpu.gpr[src])) || 
            *((UINT32 *)&thread_ctx->vcpu.gpr[dst]))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
#endif
	/* temporary tag value */
	uint8_t src_tag = *((uint8_t *)&thread_ctx->vcpu.gpr[src]);

	/* update the destination (xfer) */
	*((uint8_t *)&thread_ctx->vcpu.gpr[dst])	= src_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 1)	= src_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 2)	= src_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 3)	= src_tag;
#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 2, POST, GPR32, dst, GPR8, src);
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate and extend tag from a 16-bit register 
 * to a 32-bit register as t[dst] = t[src]
 *
 * NOTE: special case for MOVSX instruction
 * and CWDE
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
sx_r2r_oplw(thread_ctx_t *thread_ctx, UINT32 dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint16_t *)&thread_ctx->vcpu.gpr[src])) || 
            thread_ctx->vcpu.gpr[dst])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
#endif
	/* temporary tag value */
	uint16_t src_tag = *((uint16_t *)&thread_ctx->vcpu.gpr[src]);

	/* update the destination (xfer) */
	*((uint16_t *)&thread_ctx->vcpu.gpr[dst])	= src_tag;
	*(((uint16_t *)&thread_ctx->vcpu.gpr[dst]) + 1)	= src_tag;
    
    // Clear the upper 32 bits
    *((UINT32 *)&thread_ctx->vcpu.gpr[dst] + 1) = TAG_ZERO;

#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 2, POST, GPR32, dst, GPR16, src);
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate and extend tag from a 32-bit register 
 * to a 64-bit register as t[dst] = t[src]
 *
 * NOTE: special case for MOVSX instruction
 * and CWQE
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
sx_r2r_opqwl(thread_ctx_t *thread_ctx, UINT32 dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.gpr[src] || thread_ctx->vcpu.gpr[dst])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
#endif
	/* temporary tag value */
	UINT32 src_tag = *((UINT32 *)&thread_ctx->vcpu.gpr[src]);

	/* update the destination (xfer) */
	*((UINT32 *)&thread_ctx->vcpu.gpr[dst])	= src_tag;
	*(((UINT32 *)&thread_ctx->vcpu.gpr[dst]) + 1)	= src_tag;
#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 2, POST, GPR64, dst, GPR32, src);
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate and extend tag between a 16-bit 
 * register and an 8-bit memory location as
 * t[dst] = t[src]
 *
 * NOTE: special case for MOVSX instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source memory address
 */
 void PIN_FAST_ANALYSIS_CALL
sx_m2r_opwb(thread_ctx_t *thread_ctx, UINT32 dst, ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((uint8_t *)(get_tag_address(src))) || 
            *(((uint16_t *)&thread_ctx->vcpu.gpr[dst])))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
#endif

	/* temporary tag value */
	uint8_t src_tag = *((uint8_t *)(get_tag_address(src)));

	/* update the destination (xfer) */
	*((uint8_t *)&thread_ctx->vcpu.gpr[dst])	= src_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 1)	= src_tag;
#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 2, POST, GPR16, dst, M8, src);
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate and extend tag between a 32-bit 
 * register and an 8-bit memory location as
 * t[dst] = t[src]
 *
 * NOTE: special case for MOVSX instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source memory address
 */
 void PIN_FAST_ANALYSIS_CALL
sx_m2r_oplb(thread_ctx_t *thread_ctx, UINT32 dst, ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((uint8_t *)(get_tag_address(src))) || thread_ctx->vcpu.gpr[dst])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
#endif

	/* temporary tag value */
	uint8_t src_tag = *((uint8_t *)(get_tag_address(src)));

	/* update the destination (xfer) */
	*((uint8_t *)&thread_ctx->vcpu.gpr[dst])	= src_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 1)	= src_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 2)	= src_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 3)	= src_tag;

    //clear the upper 32 bits
    *((UINT32 *)&thread_ctx->vcpu.gpr[dst] + 1) = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 2, POST, GPR32, dst, M8, src);
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate and extend tag between a 32-bit register
 * and a 16-bit register as t[dst] = t[src]
 *
 * NOTE: special case for MOVSX instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
sx_m2r_oplw(thread_ctx_t *thread_ctx, UINT32 dst, ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((uint16_t *)(get_tag_address(src))) || 
            thread_ctx->vcpu.gpr[dst])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
#endif

	/* temporary tag value */
	uint16_t src_tag =  *((uint16_t *)(get_tag_address(src)));

	/* update the destination (xfer) */
	*((uint16_t *)&thread_ctx->vcpu.gpr[dst])	= src_tag;
	*((uint16_t *)&thread_ctx->vcpu.gpr[dst] + 1)	= src_tag;

    //clear the upper 32 bits
    *((UINT32 *)&thread_ctx->vcpu.gpr[dst]) = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 2, POST, GPR32, dst, M16, src);
#endif
}



/*
 * tag propagation (analysis function)
 *
 * propagate and extend tag between a 64-bit 
 * register and an 8-bit memory location as
 * t[dst] = t[src]
 *
 * NOTE: special case for MOVSX instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source memory address
 */
 void PIN_FAST_ANALYSIS_CALL
sx_m2r_opqwb(thread_ctx_t *thread_ctx, UINT32 dst, ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((uint8_t *)(get_tag_address(src))) || thread_ctx->vcpu.gpr[dst])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
#endif
	/* temporary tag value */
	uint8_t src_tag = *((uint8_t *)(get_tag_address(src)));

	/* update the destination (xfer) */
	*((uint8_t *)&thread_ctx->vcpu.gpr[dst])	= src_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 1)	= src_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 2)	= src_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 3)	= src_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 4) = src_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 5)	= src_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 6)	= src_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 7)	= src_tag;

#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src: %lx - taint 0x%x dst reg: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint8_t *)(get_tag_address(src))),
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate and extend tag between a 64-bit register
 * and a 32-bit register as t[dst] = t[src]
 *
 * NOTE: special case for MOVSX instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
sx_m2r_opqwl(thread_ctx_t *thread_ctx, UINT32 dst, ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((UINT32 *)(get_tag_address(src))) || 
            thread_ctx->vcpu.gpr[dst])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
#endif
	/* temporary tag value */
	UINT32 src_tag =  *((UINT32 *)(get_tag_address(src)));

	/* update the destination (xfer) */
	*((UINT32 *)&thread_ctx->vcpu.gpr[dst])	= src_tag;
	*(((UINT32 *)&thread_ctx->vcpu.gpr[dst]) + 1)	= src_tag;

#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 2, POST, GPR64, dst, M32, src);
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate and extend tag between a 64-bit register
 * and a 16-bit register as t[dst] = t[src]
 *
 * NOTE: special case for MOVSX instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
sx_m2r_opqww(thread_ctx_t *thread_ctx, UINT32 dst, ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((uint16_t *)(get_tag_address(src))) || 
            thread_ctx->vcpu.gpr[dst])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
#endif

	/* temporary tag value */
	uint16_t src_tag =  *((uint16_t *)(get_tag_address(src)));

	/* update the destination (xfer) */
	*((uint16_t *)&thread_ctx->vcpu.gpr[dst])	= src_tag;
	*(((uint16_t *)&thread_ctx->vcpu.gpr[dst]) + 1)	= src_tag;
	*(((uint16_t *)&thread_ctx->vcpu.gpr[dst]) + 2)	= src_tag;
	*(((uint16_t *)&thread_ctx->vcpu.gpr[dst]) + 3)	= src_tag;
#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 2, POST, GPR64, dst, M16, src);
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate and extend tag from an upper 8-bit register
 * to a 16-bit register as t[dst] = t[upper(src)]
 *
 * NOTE: special case for MOVZX instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
zx_r2r_opwb_u(thread_ctx_t *thread_ctx, UINT32 dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1) || 
            *((uint16_t *)&thread_ctx->vcpu.gpr[dst]))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
#endif
	/* temporary tag value */
	uint8_t src_tag = *(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1);

	/* update the destination (xfer) */
	*((uint16_t *)&thread_ctx->vcpu.gpr[dst])	= src_tag;
#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 2, POST, GPR16, dst, GPR8H, src);
#endif

}

/*
 * tag propagation (analysis function)
 *
 * propagate and extend tag between a 16-bit 
 * register and an 8-bit register as t[dst] = t[lower(src)]
 *
 * NOTE: special case for MOVZX instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
zx_r2r_opwb_l(thread_ctx_t *thread_ctx, UINT32 dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint8_t *)&thread_ctx->vcpu.gpr[src])) || 
            *((uint16_t *)&thread_ctx->vcpu.gpr[dst]))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
#endif
	/* temporary tag value */
	uint8_t src_tag = *((uint8_t *)&thread_ctx->vcpu.gpr[src]);

	/* update the destination (xfer) */
	*((uint16_t *)&thread_ctx->vcpu.gpr[dst])	= src_tag;
#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 2, POST, GPR16, dst, GPR8, src);
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate and extend tag between a 64-bit register
 * and an upper 8-bit register as t[dst] = t[upper(src)]
 *
 * NOTE: special case for MOVZX instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
zx_r2r_opqwb_u(thread_ctx_t *thread_ctx, UINT32 dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1) || 
            thread_ctx->vcpu.gpr[dst])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
#endif
	/* temporary tag value */
	uint8_t src_tag = *(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1);

	/* update the destination (xfer) */
	thread_ctx->vcpu.gpr[dst] = src_tag;

#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 2, POST, GPR64, dst, GPR8H, src);
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate and extend tag between a 64-bit register
 * and a lower 8-bit register as t[dst] = t[lower(src)]
 *
 * NOTE: special case for MOVZX instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
zx_r2r_opqwb_l(thread_ctx_t *thread_ctx, UINT32 dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((uint8_t *)&thread_ctx->vcpu.gpr[src]) || 
            thread_ctx->vcpu.gpr[dst])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
#endif
	/* temporary tag value */
	uint8_t src_tag = *((uint8_t *)&thread_ctx->vcpu.gpr[src]);

	/* update the destination (xfer) */
	thread_ctx->vcpu.gpr[dst] = src_tag;
#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 2, POST, GPR64, dst, GPR8, src);
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate and extend tag between a 32-bit register
 * and a 16-bit register as t[dst] = t[src]
 *
 * NOTE: special case for MOVZX instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
zx_r2r_oplw(thread_ctx_t *thread_ctx, UINT32 dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((uint16_t *)&thread_ctx->vcpu.gpr[src]) || thread_ctx->vcpu.gpr[dst])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x dst reg: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(), 
                src, *(((uint16_t *)&thread_ctx->vcpu.gpr[src])),
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
	/* temporary tag value */
	uint16_t src_tag = *((uint16_t *)&thread_ctx->vcpu.gpr[src]);

	/* update the destination (xfer) */
	thread_ctx->vcpu.gpr[dst] = src_tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x dst reg: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(), 
                src, *(((uint16_t *)&thread_ctx->vcpu.gpr[src])),
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate and extend tag between a 32-bit register
 * and an upper 8-bit register as t[dst] = t[upper(src)]
 *
 * NOTE: special case for MOVZX instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
zx_r2r_oplb_u(thread_ctx_t *thread_ctx, UINT32 dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1) || 
            thread_ctx->vcpu.gpr[dst])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x dst reg: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(), 
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1),
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
	/* temporary tag value */
	uint8_t src_tag = *(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1);

	/* update the destination (xfer) */
	*((UINT32 *)&thread_ctx->vcpu.gpr[dst])	= src_tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x dst reg: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(), 
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1),
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate and extend tag between a 32-bit register
 * and a lower 8-bit register as t[dst] = t[lower(src)]
 *
 * NOTE: special case for MOVZX instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
zx_r2r_oplb_l(thread_ctx_t *thread_ctx, UINT32 dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((uint8_t *)&thread_ctx->vcpu.gpr[src]) || 
            thread_ctx->vcpu.gpr[dst])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x dst reg: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(), 
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src])),
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
	/* temporary tag value */
	uint8_t src_tag = *((uint8_t *)&thread_ctx->vcpu.gpr[src]);

	/* update the destination (xfer) */
	*((UINT32 *)&thread_ctx->vcpu.gpr[dst])	= src_tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x dst reg: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(), 
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src])),
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
}


/*
 * tag propagation (analysis function)
 *
 * propagate and extend tag between a 16-bit 
 * register and an 8-bit memory location as
 * t[dst] = t[src]
 *
 * NOTE: special case for MOVZX instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source memory address
 */
 void PIN_FAST_ANALYSIS_CALL
zx_m2r_opwb(thread_ctx_t *thread_ctx, UINT32 dst, ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((uint8_t *)(get_tag_address(src))) || 
            *(((uint16_t *)&thread_ctx->vcpu.gpr[dst])))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint8_t *)(get_tag_address(src))),
                dst, *(((uint16_t *)&thread_ctx->vcpu.gpr[dst])));
#endif
	/* temporary tag value */
	uint8_t src_tag = *((uint8_t *)(get_tag_address(src)));

	/* update the destination (xfer) */
	*((uint16_t *)&thread_ctx->vcpu.gpr[dst])	= src_tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted){
        printLog("Post %s: src: %lx - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint8_t *)(get_tag_address(src))),
                dst, *(((uint16_t *)&thread_ctx->vcpu.gpr[dst])));
    }
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate and extend tag between a 32-bit 
 * register and an 8-bit memory location as
 * t[dst] = t[src]
 *
 * NOTE: special case for MOVZX instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source memory address
 */
 void PIN_FAST_ANALYSIS_CALL
zx_m2r_oplb(thread_ctx_t *thread_ctx, UINT32 dst, ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((uint8_t *)(get_tag_address(src))) || 
            thread_ctx->vcpu.gpr[dst])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint 0x%x dst reg: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint8_t *)(get_tag_address(src))),
                dst, thread_ctx->vcpu.gpr[dst]);
#endif

	/* temporary tag value */
	uint8_t src_tag = *((uint8_t *)(get_tag_address(src)));

	/* update the destination (xfer) */
	*((UINT32 *)&thread_ctx->vcpu.gpr[dst])	= src_tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted){
        printLog("Post %s: src: %lx - taint 0x%x dst reg: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint8_t *)(get_tag_address(src))),
                dst, thread_ctx->vcpu.gpr[dst]);
    }
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate and extend tag between a 32-bit register
 * and a 16-bit register as t[dst] = t[src]
 *
 * NOTE: special case for MOVZX instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
zx_m2r_oplw(thread_ctx_t *thread_ctx, UINT32 dst, ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((uint16_t *)(get_tag_address(src))) || thread_ctx->vcpu.gpr[dst])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint 0x%x dst reg: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint16_t *)(get_tag_address(src))),
                dst, thread_ctx->vcpu.gpr[dst]);
#endif

	/* temporary tag value */
	uint16_t src_tag =  *((uint16_t *)(get_tag_address(src)));

	/* update the destination (xfer) */
	*((UINT32 *)&thread_ctx->vcpu.gpr[dst])	= src_tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted){
        printLog("Post %s: src: %lx - taint 0x%x dst reg: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint16_t *)(get_tag_address(src))),
                dst, thread_ctx->vcpu.gpr[dst]);
    }
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate and extend tag between a 64-bit 
 * register and an 8-bit memory location as
 * t[dst] = t[src]
 *
 * NOTE: special case for MOVZX instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source memory address
 */
 void PIN_FAST_ANALYSIS_CALL
zx_m2r_opqwb(thread_ctx_t *thread_ctx, UINT32 dst, ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((uint8_t *)(get_tag_address(src))) || 
            thread_ctx->vcpu.gpr[dst])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint 0x%x dst reg: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint8_t *)(get_tag_address(src))),
                dst, thread_ctx->vcpu.gpr[dst]);
#endif

	/* temporary tag value */
	uint8_t src_tag = *((uint8_t *)(get_tag_address(src)));

	/* update the destination (xfer) */
	thread_ctx->vcpu.gpr[dst] = src_tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted){
        printLog("Post %s: src: %lx - taint 0x%x dst reg: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint8_t *)(get_tag_address(src))),
                dst, thread_ctx->vcpu.gpr[dst]);
    }
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate and extend tag between a 64-bit register
 * and a 16-bit register as t[dst] = t[src]
 *
 * NOTE: special case for MOVZX instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
zx_m2r_opqww(thread_ctx_t *thread_ctx, 
        UINT32 dst, ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((uint16_t *)(get_tag_address(src))) || thread_ctx->vcpu.gpr[dst])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint 0x%x dst reg: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint16_t *)(get_tag_address(src))),
                dst, thread_ctx->vcpu.gpr[dst]);
#endif

	/* temporary tag value */
	uint16_t src_tag =  *((uint16_t *)(get_tag_address(src)));

	/* update the destination (xfer) */
	thread_ctx->vcpu.gpr[dst] = src_tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted){
        printLog("Post %s: src: %lx - taint 0x%x dst reg: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint16_t *)(get_tag_address(src))),
                dst, thread_ctx->vcpu.gpr[dst]);
    }
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between two 64-bit
 * registers as t[RAX] = t[src]; return
 * the result of RAX == src and also
 * store the original tag value of
 * RAX in the scratch register
 *
 * NOTE: special case for the CMPXCHG instruction
 *
 * @thread_ctx:	the thread context
 * @dst_val:	RAX register value
 * @src:	source register index (VCPU)
 * @src_val:	source register value
 */
 ADDRINT PIN_FAST_ANALYSIS_CALL
_cmpxchg_r2r_opl_fast(thread_ctx_t *thread_ctx, ADDRINT dst_val, UINT32 src,
							ADDRINT src_val, UINT32 opcode)
{
    UINT32 dst = RAX;
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.gpr[src] || thread_ctx->vcpu.gpr[dst])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: reg: %u - taint 0x%x reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, thread_ctx->vcpu.gpr[src],
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
	/* save the tag value of dst in the scratch register */
	thread_ctx->vcpu.gpr[GPR_SCRATCH] = 
		thread_ctx->vcpu.gpr[dst];

	/* update */
	thread_ctx->vcpu.gpr[dst] =
		thread_ctx->vcpu.gpr[src];

#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted && dst_val == src_val)
        printLog("Post %s eq: src reg: %u - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, thread_ctx->vcpu.gpr[src],
                dst, thread_ctx->vcpu.gpr[dst]);
#endif

	/* compare the dst and src values */
	return (dst_val == src_val);
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between two 64-bit 
 * registers as t[dst] = t[src]; restore the
 * value of RAX from the scratch register
 *
 * NOTE: special case for the CMPXCHG instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
_cmpxchg_r2r_opl_slow(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src, UINT32 opcode)
{
	UINT32 cmp_reg = RAX;
    /* restore the tag value from the scratch register */
	thread_ctx->vcpu.gpr[cmp_reg] = 
		thread_ctx->vcpu.gpr[GPR_SCRATCH];
	
	/* update */
	thread_ctx->vcpu.gpr[dst] =
		thread_ctx->vcpu.gpr[src];
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && (thread_ctx->vcpu.gpr[src] || thread_ctx->vcpu.gpr[dst]))
        printLog("Post %s neq: src reg: %u - taint %lu \
                dst reg: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, thread_ctx->vcpu.gpr[src],
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
}


/*
 * tag propagation (analysis function)
 *
 * propagate tag between two 16-bit
 * registers as t[AX] = t[src]; return
 * the result of AX == src and also
 * store the original tag value of
 * AX in the scratch register
 *
 * NOTE: special case for the CMPXCHG instruction
 *
 * @thread_ctx:	the thread context
 * @dst_val:	AX register value
 * @src:	source register index (VCPU)
 * @src_val:	source register value
 */
 ADDRINT PIN_FAST_ANALYSIS_CALL
_cmpxchg_r2r_opw_fast(thread_ctx_t *thread_ctx, ADDRINT dst_val, UINT32 src,
						UINT32 src_val, UINT32 opcode)
{
    UINT32 dst = AX;
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((uint16_t *)&thread_ctx->vcpu.gpr[src]) || 
            *((uint16_t *)&thread_ctx->vcpu.gpr[dst]))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: reg: %u - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint16_t *)&thread_ctx->vcpu.gpr[src]),
                dst, *((uint16_t *)&thread_ctx->vcpu.gpr[dst]));
#endif
	/* save the tag value of dst in the scratch register */
	thread_ctx->vcpu.gpr[GPR_SCRATCH] = 
		thread_ctx->vcpu.gpr[dst];
	
	/* update */
	*((uint16_t *)&thread_ctx->vcpu.gpr[dst]) = 
        *((uint16_t *)&thread_ctx->vcpu.gpr[src]);

#ifdef PROPAGATION_DEBUG
    if(postPropFlag && dst_val == src_val && tainted)
        printLog("Post %s e: src reg: %u - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint16_t *)&thread_ctx->vcpu.gpr[src]),
                dst, *((uint16_t *)&thread_ctx->vcpu.gpr[dst]));
#endif
	/* compare the dst and src values */
	return ((UINT16)dst_val == (UINT16)src_val);
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between two 16-bit 
 * registers as t[dst] = t[src]; restore the
 * value of AX from the scratch register
 *
 * NOTE: special case for the CMPXCHG instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
_cmpxchg_r2r_opw_slow(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, UINT32 opcode)
{
	UINT32 cmp_reg = AX;
    /* restore the tag value from the scratch register */
	thread_ctx->vcpu.gpr[cmp_reg] = 
		thread_ctx->vcpu.gpr[GPR_SCRATCH];
	
	/* update */
	*((uint16_t *)&thread_ctx->vcpu.gpr[dst]) =
		*((uint16_t *)&thread_ctx->vcpu.gpr[src]);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && (*(&thread_ctx->vcpu.gpr[src]) || 
                *(&thread_ctx->vcpu.gpr[src])))
        printLog("Post %s neq: src reg: %u - taint 0x%x \
                dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint16_t *)&thread_ctx->vcpu.gpr[src]),
                dst, *((uint16_t *)&thread_ctx->vcpu.gpr[dst]));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between a 64-bit
 * register and a memory location
 * as t[RAX] = t[src]; return the result
 * of RAX == src and also store the
 * original tag value of RAX in
 * the scratch register
 *
 * NOTE: special case for the CMPXCHG instruction
 *
 * @thread_ctx:	the thread context
 * @dst_val:	destination register value
 * @src:	source memory address
 */
 ADDRINT PIN_FAST_ANALYSIS_CALL
_cmpxchg_m2r_opqw_fast(thread_ctx_t *thread_ctx, 
        ADDRINT dst_val, ADDRINT src, UINT32 opcode)
{
    UINT32 dst = RAX;
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if( *(ADDRINT *)get_tag_address(src) || thread_ctx->vcpu.gpr[dst])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: mem: %lx - taint %lu reg: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(ADDRINT *)(get_tag_address(src)),
                dst, thread_ctx->vcpu.gpr[dst]);
#endif

	/* save the tag value of dst in the scratch register */
	thread_ctx->vcpu.gpr[GPR_SCRATCH] = 
		thread_ctx->vcpu.gpr[dst];
	
	/* update */
	thread_ctx->vcpu.gpr[dst] = 
		*(ADDRINT *)(get_tag_address(src));
	
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && *(ADDRINT *)src == dst_val && tainted) 
        printLog("Post %s ne: src mem: %lx - taint %lu dst reg: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(ADDRINT *)get_tag_address(src),
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
	/* compare the dst and src values; the original values the tag bits */
	return (dst_val == *(ADDRINT *)src);
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between a 64-bit 
 * register and a memory location
 * as t[dst] = t[src]; restore the value
 * of RAX from the scratch register
 *
 * NOTE: special case for the CMPXCHG instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination memory address
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
_cmpxchg_r2m_opqw_slow(thread_ctx_t *thread_ctx, 
        ADDRINT dst, UINT32 src, UINT32 opcode)
{
	/* restore the tag value from the scratch register */
	thread_ctx->vcpu.gpr[RAX] = 
		thread_ctx->vcpu.gpr[GPR_SCRATCH];
	
	/* update */
	*(ADDRINT *)get_tag_address(dst)=
		thread_ctx->vcpu.gpr[src];
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && ((thread_ctx->vcpu.gpr[src]) || *(ADDRINT *)get_tag_address(dst)))
        printLog("Post %s ne: src reg: %u - taint %lu dst mem: %lx - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, thread_ctx->vcpu.gpr[src],
                dst, *(ADDRINT *)(get_tag_address(dst)));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between a 32-bit
 * register and a memory location
 * as t[RAX] = t[src]; return the result
 * of RAX == src and also store the
 * original tag value of RAX in
 * the scratch register
 *
 * NOTE: special case for the CMPXCHG instruction
 *
 * @thread_ctx:	the thread context
 * @dst_val:	destination register value
 * @src:	source memory address
 */
 ADDRINT PIN_FAST_ANALYSIS_CALL
_cmpxchg_m2r_opl_fast(thread_ctx_t *thread_ctx, 
        ADDRINT dst_val, ADDRINT src, UINT32 opcode)
{
    UINT32 dst = RAX;
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if( *((UINT32 *)(get_tag_address(src))) || thread_ctx->vcpu.gpr[dst])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: mem: %lx - taint 0x%x reg: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((UINT32 *)(get_tag_address(src))),
                dst, thread_ctx->vcpu.gpr[dst]);
#endif

	/* save the tag value of dst in the scratch register */
	thread_ctx->vcpu.gpr[GPR_SCRATCH] = 
		thread_ctx->vcpu.gpr[dst];
	
	/* update */
    m2r_mov_32(thread_ctx, dst, src);
	
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && *(UINT32 *)src == (UINT32)dst_val && tainted) 
        printLog("Post %s ne: src mem: %lx - taint 0x%x dst reg: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((UINT32 *)(get_tag_address(src))),
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
	/* compare the dst and src values; the original values the tag bits */
	return (dst_val == *(UINT32 *)src);
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between a 32-bit 
 * register and a memory location
 * as t[dst] = t[src]; restore the value
 * of RAX from the scratch register
 *
 * NOTE: special case for the CMPXCHG instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination memory address
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
_cmpxchg_r2m_opl_slow(thread_ctx_t *thread_ctx, 
        ADDRINT dst, UINT32 src, UINT32 opcode)
{
    UINT32 cmp_reg = RAX;
    /* restore the tag value from the scratch register */
	thread_ctx->vcpu.gpr[cmp_reg] = 
		thread_ctx->vcpu.gpr[GPR_SCRATCH];
	
	/* update */
	*((UINT32 *)(get_tag_address(dst))) =
		*((UINT32 *)&thread_ctx->vcpu.gpr[src]);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && ((thread_ctx->vcpu.gpr[src]) || *((UINT32 *)(get_tag_address(dst)))))
        printLog("Post %s ne: src reg: %lu - taint 0x%x dst mem: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, thread_ctx->vcpu.gpr[src],
                dst, *((UINT32 *)(get_tag_address(dst))));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between a 16-bit
 * register and a memory location
 * as t[AX] = t[src]; return the result
 * of AX == src and also store the
 * original tag value of AX in
 * the scratch register
 *
 * NOTE: special case for the CMPXCHG instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @dst_val:	destination register value
 * @src:	source memory address
 */
 ADDRINT PIN_FAST_ANALYSIS_CALL
_cmpxchg_m2r_opw_fast(thread_ctx_t *thread_ctx, 
        ADDRINT dst_val, ADDRINT src, UINT32 opcode)
{
    UINT32 dst = AX;
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((uint16_t *)(get_tag_address(src))) || *(((uint16_t *)&thread_ctx->vcpu.gpr[dst])))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: mem: %lx - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint16_t *)(get_tag_address(src))),
                dst, *(((uint16_t *)&thread_ctx->vcpu.gpr[dst])));
#endif

	/* save the tag value of dst in the scratch register */
	thread_ctx->vcpu.gpr[GPR_SCRATCH] = 
		thread_ctx->vcpu.gpr[dst];
	
	/* update */
	*((uint16_t *)&thread_ctx->vcpu.gpr[dst]) = 
		*((uint16_t *)(get_tag_address(src)));
	
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && (*(UINT16 *)dst_val == *(uint16_t *)src) && tainted)
        printLog("Post %s e: src mem: %lx - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint16_t *)(get_tag_address(src))),
                dst, *(((uint16_t *)&thread_ctx->vcpu.gpr[dst])));
#endif
	/* compare the dst and src values; the original values the tag bits */
	return (*(UINT16 *)dst_val == *(uint16_t *)src);
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between a 16-bit 
 * register and a memory location
 * as t[dst] = t[src]; restore the value
 * of AX from the scratch register
 *
 * NOTE: special case for the CMPXCHG instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination memory address
 * @src:	source register index (VCPU)
 * @res:	restore register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
_cmpxchg_r2m_opw_slow(thread_ctx_t *thread_ctx, 
        ADDRINT dst, UINT32 src, UINT32 opcode)
{
    UINT32 cmp_reg = AX;
    /* restore the tag value from the scratch register */
	thread_ctx->vcpu.gpr[cmp_reg] = 
		thread_ctx->vcpu.gpr[GPR_SCRATCH];
	
	/* update */
	*((uint16_t *)(get_tag_address(dst))) =
		*((uint16_t *)&thread_ctx->vcpu.gpr[src]);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && (*(((uint16_t *)&thread_ctx->vcpu.gpr[src])) || 
                *((uint16_t *)(get_tag_address(dst)))))
        printLog("Post %s ne: src reg: %u - taint 0x%x dst mem: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint16_t *)&thread_ctx->vcpu.gpr[src])),
                dst, *((uint16_t *)(get_tag_address(dst))));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between the 64-bit value in RDX:RAX
 * and a memory location. This is the case where the values
 * are not equal, so copy dst tag to RDX:RAX. Store the tag
 * of RDX:RAX in the 64-bit scratch register
 * 
 * NOTE: special case for the CMPXCHG8B instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	64-bit destination memory address
 * @src:	value of RDX
 * @res:	value of RAX
 */
 ADDRINT PIN_FAST_ANALYSIS_CALL
cmpxchg8_r2m_neq(thread_ctx_t *thread_ctx, 
        ADDRINT dst, ADDRINT src1_val, ADDRINT src2_val, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(ADDRINT *)get_tag_address(dst) || thread_ctx->vcpu.gpr[RDX] ||
            thread_ctx->vcpu.gpr[RAX])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: mem: %lx - taint %lu \
                RDX taint %lu RAX taint: %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(ADDRINT *)get_tag_address(dst), 
                thread_ctx->vcpu.gpr[RDX],
                thread_ctx->vcpu.gpr[RAX]);
#endif
    // Store RDX: RAX tag
    *((UINT32 *)&thread_ctx->vcpu.gpr[GPR_SCRATCH]) = 
        *((UINT32 *)&thread_ctx->vcpu.gpr[RAX]);
    *((UINT32 *)&thread_ctx->vcpu.gpr[GPR_SCRATCH] + 1) = 
        *((UINT32 *)&thread_ctx->vcpu.gpr[RDX]); 
    
    // propagate taint
    *((UINT32 *)&thread_ctx->vcpu.gpr[RAX]) = 
        *(UINT32 *)get_tag_address(dst);
    *((UINT32 *)&thread_ctx->vcpu.gpr[RDX]) = 
        *(UINT32 *)get_tag_address(dst + sizeof(UINT32));
	
    UINT64 reg_val = (((UINT32)src1_val) << 5) + (UINT32)src2_val;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted && (reg_val == *(ADDRINT *)dst))
        printLog("Post %s: mem: %lx - taint %lu \
                RDX taint %lu RAX taint: %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, 
                *(ADDRINT *)get_tag_address(dst), 
                thread_ctx->vcpu.gpr[RDX],
                thread_ctx->vcpu.gpr[RAX]);
#endif
    return (reg_val == *(ADDRINT *)dst);
} 


/*
 * tag propagation (analysis function)
 *
 * propagate tag between the 64-bit value in RCX:RBX
 * and a memory location. This is the case where the values
 * are equal, so copy RCX:RBX tag to dst tag. 
 * 
 * NOTE: special case for the CMPXCHG8B instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	64-bit destination memory address
 * @src:	value of RCX
 * @res:	value of RBX
 */
 void  PIN_FAST_ANALYSIS_CALL
cmpxchg8_r2m_eq(thread_ctx_t *thread_ctx, 
        ADDRINT dst, ADDRINT src1_val, ADDRINT src2_val, UINT32 opcode)
{
    //Restore rdx:rax
    *((UINT32 *)&thread_ctx->vcpu.gpr[RAX]) = 
        *((UINT32 *)&thread_ctx->vcpu.gpr[GPR_SCRATCH]); 
    *((UINT32 *)&thread_ctx->vcpu.gpr[RDX]) =
        *((UINT32 *)&thread_ctx->vcpu.gpr[GPR_SCRATCH] + 1); 
    
    *(UINT32 *)get_tag_address(dst) = (UINT32)src2_val;
    *(UINT32 *)get_tag_address(dst + sizeof(UINT32)) = (UINT32)src1_val;
	
#ifdef PROPAGATION_DEBUG
    if(postPropFlag)
        printLog("Post %s eq: mem: %lx - taint %lu \
                RDX taint %lu RAX taint: %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, 
                *(ADDRINT *)get_tag_address(dst), 
                thread_ctx->vcpu.gpr[RDX],
                thread_ctx->vcpu.gpr[RAX]);
#endif
} 


/*
 * tag propagation (analysis function)
 *
 * propagate tag between the 128-bit value in RDX:RAX
 * and a memory location. This is the case where the values
 * are not equal, so copy dst tag to RDX:RAX. Store the tag
 * of RDX:RAX in the 128-bit xmm scratch register
 * 
 * NOTE: special case for the CMPXCHG16B instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	128-bit destination memory address
 * @src:	value of RDX
 * @res:	value of RAX
 */
 ADDRINT PIN_FAST_ANALYSIS_CALL
cmpxchg16_r2m_neq(thread_ctx_t *thread_ctx, 
        ADDRINT dst, ADDRINT src1_val, ADDRINT src2_val, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(uint128_t *)get_tag_address(dst) || thread_ctx->vcpu.gpr[RDX] ||
            thread_ctx->vcpu.gpr[RAX])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: mem: %lx - taint %lu-%lu \
                RDX taint %lu RAX taint: %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(ADDRINT *)get_tag_address(dst), 
                *(ADDRINT *)get_tag_address(dst + sizeof(ADDRINT)),
                thread_ctx->vcpu.gpr[RDX],
                thread_ctx->vcpu.gpr[RAX]);
#endif
    // Store RDX: RAX tag
    *((UINT64 *)&thread_ctx->vcpu.avx[AVX_SCRATCH]) = 
        thread_ctx->vcpu.gpr[RAX];
    *((UINT64 *)&thread_ctx->vcpu.avx[AVX_SCRATCH] + 1) = 
        thread_ctx->vcpu.gpr[RDX]; 
    
    // propagate taint
    thread_ctx->vcpu.gpr[RAX] = 
        *(UINT64 *)get_tag_address(dst);
    thread_ctx->vcpu.gpr[RDX] = 
        *(UINT64 *)get_tag_address(dst + sizeof(UINT64));
	
    uint128_t reg_val = (src1_val << 6) + src2_val;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted && (reg_val == *(uint128_t *)dst))
        printLog("Post %s: mem: %lx - taint %lu-%lu \
                RDX taint %lu RAX taint: %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, 
                *(ADDRINT *)get_tag_address(dst), 
                *(ADDRINT *)get_tag_address(dst + sizeof(ADDRINT)),
                thread_ctx->vcpu.gpr[RDX],
                thread_ctx->vcpu.gpr[RAX]);
#endif
    return (reg_val == *(uint128_t *)dst);
} 


/*
 * tag propagation (analysis function)
 *
 * propagate tag between the 128-bit value in RDX:RAX
 * and a memory location. This is the case where the values
 * are equal, so copy RCX:RBX tag to dst tag. 
 * 
 * NOTE: special case for the CMPXCHG16B instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	128-bit destination memory address
 * @src:	value of RCX
 * @res:	value of RBX
 */
 void  PIN_FAST_ANALYSIS_CALL
cmpxchg16_r2m_eq(thread_ctx_t *thread_ctx, 
        ADDRINT dst, ADDRINT src1_val, ADDRINT src2_val, UINT32 opcode)
{
    //Restore rdx:rax
    thread_ctx->vcpu.gpr[RAX] = 
        *((UINT64 *)&thread_ctx->vcpu.avx[AVX_SCRATCH]); 
    thread_ctx->vcpu.gpr[RDX] =
        *((UINT64 *)&thread_ctx->vcpu.avx[AVX_SCRATCH] + 1); 
    
    *(ADDRINT *)get_tag_address(dst) = src2_val;
    *(ADDRINT *)get_tag_address(dst + sizeof(ADDRINT)) = src1_val;
	
#ifdef PROPAGATION_DEBUG
    if(postPropFlag)
        printLog("Post %s eq: mem: %lx - taint %lu-%lu \
                RDX taint %lu RAX taint: %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, 
                *(ADDRINT *)get_tag_address(dst), 
                *(ADDRINT *)get_tag_address(dst + sizeof(ADDRINT)),
                thread_ctx->vcpu.gpr[RDX],
                thread_ctx->vcpu.gpr[RAX]);
#endif
} 

/*
 * tag propagation (analysis function)
 *
 * propagate tag from a 64-bit memory location
 * to a 64-bit register as
 * t[dst] = t[src] and t[src] = t[dst] 
 * (src is a register)
 *
 * NOTE: special case for the XCHG instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination memory address
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
_xchg_r2m_opqw(thread_ctx_t *thread_ctx, 
        ADDRINT dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.gpr[src] || *(ADDRINT *)get_tag_address(dst))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint %lu dst: %lx - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, thread_ctx->vcpu.gpr[src],
                dst, *(ADDRINT *)get_tag_address(dst));
#endif
	/* temporary tag value */
	UINT64 tmp_tag = *(ADDRINT *)get_tag_address(dst);

	/* swap */
	*(ADDRINT *)get_tag_address(dst) =
		thread_ctx->vcpu.gpr[src];
		
	thread_ctx->vcpu.gpr[src] = tmp_tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint %lu dst: %lx - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, thread_ctx->vcpu.gpr[src],
                dst, *(ADDRINT *)get_tag_address(dst));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between a 32-bit 
 * register and a memory location as
 * t[dst] = t[src] and t[src] = t[dst] 
 * (src is a register)
 *
 * NOTE: special case for the XCHG instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination memory address
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
_xchg_r2m_opl(thread_ctx_t *thread_ctx, 
        ADDRINT dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.gpr[src] || *((UINT32 *)(get_tag_address(dst))))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint %lu dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, thread_ctx->vcpu.gpr[src],
                dst, *((UINT32 *)(get_tag_address(dst))));
#endif
	/* temporary tag value */
	UINT32 tmp_tag = *((UINT32 *)(get_tag_address(dst)));

	/* swap */
	*((UINT32 *)(get_tag_address(dst))) =
		*((UINT32 *)&thread_ctx->vcpu.gpr[src]);
		
	*((UINT32 *)&thread_ctx->vcpu.gpr[src]) = tmp_tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint %lu dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, thread_ctx->vcpu.gpr[src],
                dst, *((UINT32 *)(get_tag_address(dst))));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between a 16-bit 
 * register and a memory location as
 * t[dst] = t[src] and t[src] = t[dst]
 * (src is a register)
 *
 * NOTE: special case for the XCHG instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination memory address
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
_xchg_r2m_opw(thread_ctx_t *thread_ctx, ADDRINT dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint16_t *)&thread_ctx->vcpu.gpr[src])) || *((uint16_t *)(get_tag_address(dst))))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint16_t *)&thread_ctx->vcpu.gpr[src])),
                dst, *((uint16_t *)(get_tag_address(dst))));
#endif
	/* temporary tag value */
	uint16_t tmp_tag = *((uint16_t *)(get_tag_address(dst)));

	/* swap */
	*((uint16_t *)(get_tag_address(dst))) =
		*((uint16_t *)&thread_ctx->vcpu.gpr[src]);
		
	*((uint16_t *)&thread_ctx->vcpu.gpr[src]) = tmp_tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint16_t *)&thread_ctx->vcpu.gpr[src])),
                dst, *((uint16_t *)(get_tag_address(dst))));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between an 8-bit 
 * register and a memory location as
 * t[dst] = t[upper(src)] and t[upper(src)] = t[dst]
 * (src is a register)
 *
 * NOTE: special case for the XCHG instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination memory address
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
_xchg_r2m_opb_u(thread_ctx_t *thread_ctx, ADDRINT dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1) || *((uint8_t *)(get_tag_address(dst))))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1),
                dst, *((uint8_t *)(get_tag_address(dst))));
#endif
	/* temporary tag value */
	uint8_t tmp_tag = *((uint8_t *)(get_tag_address(dst)));

	/* swap */
	*((uint8_t *)(get_tag_address(dst))) =
		*(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1);
	
	*(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1) = tmp_tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1),
                dst, *((uint8_t *)(get_tag_address(dst))));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between an 8-bit 
 * register and a memory location as
 * t[dst] = t[lower(src)] and t[lower(src)] = t[dst]
 * (src is a register)
 *
 * NOTE: special case for the XCHG instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination memory address
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
_xchg_r2m_opb_l(thread_ctx_t *thread_ctx, ADDRINT dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint8_t *)&thread_ctx->vcpu.gpr[src])) || *((uint8_t *)(get_tag_address(dst))))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src])),
                dst, *((uint8_t *)(get_tag_address(dst))));
#endif
	/* temporary tag value */
	uint8_t tmp_tag = *((uint8_t *)(get_tag_address(dst)));
	
	/* swap */
	*((uint8_t *)(get_tag_address(dst))) =
		*((uint8_t *)&thread_ctx->vcpu.gpr[src]);
	
	*((uint8_t *)&thread_ctx->vcpu.gpr[src]) = tmp_tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src])),
                dst, *((uint8_t *)(get_tag_address(dst))));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between a 64-bit 
 * register and a memory location as
 * t[dst] |= t[src] and t[src] = t[dst] 
 * (src is a register)
 *
 * NOTE: special case for the XADD instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination memory address
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
_xadd_r2m_opqw(thread_ctx_t *thread_ctx, 
        ADDRINT dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.gpr[src] || *(ADDRINT *)get_tag_address(dst))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %lu - taint 0x%x dst: %lx - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, thread_ctx->vcpu.gpr[src],
                dst, *(ADDRINT *)get_tag_address(dst));
#endif
	/* temporary tag value */
	UINT64 tmp_tag = *(ADDRINT *)get_tag_address(dst);

	/* swap */
	*(ADDRINT *)get_tag_address(dst) |= thread_ctx->vcpu.gpr[src];
		
	thread_ctx->vcpu.gpr[src] = tmp_tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %lu - taint 0x%x dst: %lx - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, thread_ctx->vcpu.gpr[src],
                dst, *(ADDRINT *)get_tag_address(dst));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between a 32-bit 
 * register and a memory location as
 * t[dst] |= t[src] and t[src] = t[dst] 
 * (src is a register)
 *
 * NOTE: special case for the XADD instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination memory address
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
_xadd_r2m_opl(thread_ctx_t *thread_ctx, ADDRINT dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.gpr[src] || *(UINT32 *)(get_tag_address(dst)))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint %lu dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, thread_ctx->vcpu.gpr[src],
                dst, *((UINT32 *)(get_tag_address(dst))));
#endif
	/* temporary tag value */
	UINT32 tmp_tag = *((UINT32 *)(get_tag_address(dst)));

	/* swap */
	*((UINT32 *)(get_tag_address(dst))) |=
		*((UINT32 *)&thread_ctx->vcpu.gpr[src]);
		
    *((UINT32 *)&thread_ctx->vcpu.gpr[src]) = tmp_tag;

#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %lu - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, thread_ctx->vcpu.gpr[src],
                dst, *((UINT32 *)(get_tag_address(dst))));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between a 16-bit 
 * register and a memory location as
 * t[dst] |= t[src] and t[src] = t[dst]
 * (src is a register)
 *
 * NOTE: special case for the XADD instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination memory address
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
_xadd_r2m_opw(thread_ctx_t *thread_ctx, ADDRINT dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint16_t *)&thread_ctx->vcpu.gpr[src])) || *((uint16_t *)(get_tag_address(dst))))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint16_t *)&thread_ctx->vcpu.gpr[src])),
                dst, *((uint16_t *)(get_tag_address(dst))));
#endif
	/* temporary tag value */
	uint16_t tmp_tag = *((uint16_t *)(get_tag_address(dst)));

	/* swap */
	*((uint16_t *)(get_tag_address(dst))) |=
		*((uint16_t *)&thread_ctx->vcpu.gpr[src]);
		
	*((uint16_t *)&thread_ctx->vcpu.gpr[src]) = tmp_tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint16_t *)&thread_ctx->vcpu.gpr[src])),
                dst, *((uint16_t *)(get_tag_address(dst))));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between an 8-bit 
 * register and a memory location as
 * t[dst] |= t[upper(src)] and t[upper(src)] = t[dst]
 * (src is a register)
 *
 * NOTE: special case for the XADD instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination memory address
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
_xadd_r2m_opb_u(thread_ctx_t *thread_ctx, ADDRINT dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1) || *((uint8_t *)(get_tag_address(dst))))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1),
                dst, *((uint8_t *)(get_tag_address(dst))));
#endif
	/* temporary tag value */
	uint8_t tmp_tag = *((uint8_t *)(get_tag_address(dst)));

	/* swap */
	*((uint8_t *)(get_tag_address(dst))) |=
		*(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1);
	
	*(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1) = tmp_tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1),
                dst, *((uint8_t *)(get_tag_address(dst))));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between an 8-bit 
 * register and a memory location as
 * t[dst] |= t[lower(src)] and t[lower(src)] = t[dst]
 * (src is a register)
 *
 * NOTE: special case for the XADD instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination memory address
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
_xadd_r2m_opb_l(thread_ctx_t *thread_ctx, ADDRINT dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint8_t *)&thread_ctx->vcpu.gpr[src])) || *((uint8_t *)(get_tag_address(dst))))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src])),
                dst, *((uint8_t *)(get_tag_address(dst))));
#endif
	/* temporary tag value */
	uint8_t tmp_tag = *((uint8_t *)(get_tag_address(dst)));
	
	/* swap */
	*((uint8_t *)(get_tag_address(dst))) |=
		*((uint8_t *)&thread_ctx->vcpu.gpr[src]);
	
	*((uint8_t *)&thread_ctx->vcpu.gpr[src]) = tmp_tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src])),
                dst, *((uint8_t *)(get_tag_address(dst))));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between three 16-bit 
 * registers as t[dst] = t[base] | t[index]
 *
 * NOTE: special case for the LEA instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register
 * @base:	base register
 * @index:	index register
 */
 void PIN_FAST_ANALYSIS_CALL
_lea_r2r_opw(thread_ctx_t *thread_ctx,
		UINT32 dst,
		UINT32 base,
		UINT32 index, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if( *((uint16_t *)&thread_ctx->vcpu.gpr[index]) || *((uint16_t *)&thread_ctx->vcpu.gpr[base]) 
            || *((uint16_t *)&thread_ctx->vcpu.gpr[dst]))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src regs: %u|%u - taints %u|%u dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                base, *((uint16_t *)&thread_ctx->vcpu.gpr[base]),
                index, *((uint16_t *)&thread_ctx->vcpu.gpr[index]),
                dst, *((uint16_t *)&thread_ctx->vcpu.gpr[dst]));
#endif
	/* update the destination */
	*((uint16_t *)&thread_ctx->vcpu.gpr[dst]) =
		*((uint16_t *)&thread_ctx->vcpu.gpr[base]) |
		*((uint16_t *)&thread_ctx->vcpu.gpr[index]); 
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src regs: %u|%u - taints %u|%u dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                base, *((uint16_t *)&thread_ctx->vcpu.gpr[base]),
                index, *((uint16_t *)&thread_ctx->vcpu.gpr[index]),
                dst, *((uint16_t *)&thread_ctx->vcpu.gpr[dst]));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between three 32-bit 
 * registers as t[dst] = t[base] | t[index]
 *
 * NOTE: special case for the LEA instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register
 * @base:	base register
 * @index:	index register
 */
 void PIN_FAST_ANALYSIS_CALL
_lea_r2r_opl(thread_ctx_t *thread_ctx,
		UINT32 dst,
		UINT32 base,
		UINT32 index, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.gpr[index] || thread_ctx->vcpu.gpr[base] ||
            thread_ctx->vcpu.gpr[dst])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src regs: %u|%u - taints %u|%u dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                base, *(&thread_ctx->vcpu.gpr[base]),
                index, *(&thread_ctx->vcpu.gpr[index]),
                dst, *(&thread_ctx->vcpu.gpr[dst]));
#endif
	/* update the destination */
	thread_ctx->vcpu.gpr[dst] =
		thread_ctx->vcpu.gpr[base] | thread_ctx->vcpu.gpr[index]; 
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src regs: %u|%u - taints %u|%u dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                base, *(&thread_ctx->vcpu.gpr[base]),
                index, *(&thread_ctx->vcpu.gpr[index]),
                dst, *(&thread_ctx->vcpu.gpr[dst]));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag among three 8-bit registers as 
 * t[dst] = t[upper(src)]| t[AL]
 * dst is AX, whereas src is an upper 8-bit register (e.g., CH, BH, ...)
 *
 * NOTE: special case for MUL and IMUL instructions
 *
 * @thread_ctx:	the thread context
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
r2r_mul_opb_u(thread_ctx_t *thread_ctx, UINT32 src, UINT32 opcode)
{
    UINT32 dst = AX;
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1) || *((uint16_t *)&thread_ctx->vcpu.gpr[dst]))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src regs: %u - taints %u dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1),
                dst, *((uint16_t *)&thread_ctx->vcpu.gpr[dst]));
#endif
	/* temporary tag value */
	uint8_t tmp_tag = *(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1) |
        *((uint8_t *)&thread_ctx->vcpu.gpr[dst]);
	
	/* update the destination (ternary) */
	*((uint8_t *)&thread_ctx->vcpu.gpr[dst]) = tmp_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 1) = tmp_tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src regs: %u - taints %u dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1),
                dst, *((uint16_t *)&thread_ctx->vcpu.gpr[dst]));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag among three 8-bit registers as 
 * t[dst] = t[lower(src)] | t[AL]
 * dst is AX, whereas src is a lower 8-bit register (e.g., CL, BL, ...)
 *
 * NOTE: special case for MUL and IMUL instructions
 *
 * @thread_ctx:	the thread context
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
r2r_mul_opb_l(thread_ctx_t *thread_ctx, UINT32 src, UINT32 opcode)
{
    UINT32 dst = AX;
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint8_t *)&thread_ctx->vcpu.gpr[src])) || *((uint16_t *)&thread_ctx->vcpu.gpr[dst]))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src regs: %u - taints %u dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src])),
                dst, *((uint16_t *)&thread_ctx->vcpu.gpr[dst]));
#endif
	/* temporary tag value */
	uint8_t tmp_tag = *((uint8_t *)&thread_ctx->vcpu.gpr[src]) |
            *((uint8_t *)&thread_ctx->vcpu.gpr[dst]);
	
	/* update the destination (ternary) */
	*((uint8_t *)&thread_ctx->vcpu.gpr[dst]) = tmp_tag;
	*((uint8_t *)&thread_ctx->vcpu.gpr[dst] + 1) = tmp_tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src regs: %u - taints %u dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src])),
                dst, *((uint16_t *)&thread_ctx->vcpu.gpr[dst]));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between among three 16-bit 
 * registers as t[dst1, dst2] = t[src] | t[AX]
 * dst1 is DX, dst2 is AX, and src is a 16-bit register 
 * (e.g., CX, BX, ...)
 *
 * NOTE: special case for MUL and IMUL instructions
 *
 * @thread_ctx:	the thread context
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
r2r_mul_opw(thread_ctx_t *thread_ctx, UINT32 src, UINT32 opcode)
{
    UINT32 dst = DX, dst2 = AX;
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint16_t *)&thread_ctx->vcpu.gpr[src])) || 
            *((uint16_t *)&thread_ctx->vcpu.gpr[dst]) ||
            *((uint16_t *)&thread_ctx->vcpu.gpr[dst2]))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src regs: %u - taints %u dst regs: %u,%u - taint %u, %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint16_t *)&thread_ctx->vcpu.gpr[src])),
                dst, *((uint16_t *)&thread_ctx->vcpu.gpr[dst]),
                dst2, *((uint16_t *)&thread_ctx->vcpu.gpr[dst2]));
#endif
	/* temporary tag value */
	uint16_t tmp_tag = *((uint16_t *)&thread_ctx->vcpu.gpr[src]) |
        *((uint16_t *)&thread_ctx->vcpu.gpr[dst2]);

	/* update the destination (ternary) */
	*((uint16_t *)&thread_ctx->vcpu.gpr[dst]) = tmp_tag;
	*((uint16_t *)&thread_ctx->vcpu.gpr[dst2]) = tmp_tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src regs: %u - taints %u dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint16_t *)&thread_ctx->vcpu.gpr[src])),
                dst, *((uint16_t *)&thread_ctx->vcpu.gpr[dst]));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between among three 32/64-bit 
 * registers as t[dst1,dst2] = t[src] | t[R/RAX] 
 * dst1 is RDX, dst2 is RAX, and src is a 32/64-bit register
 * (e.g., RCX, RBX, ...)
 *
 * NOTE: special case for MUL and IMUL instructions
 *
 * @thread_ctx:	the thread context
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
r2r_mul_opl(thread_ctx_t *thread_ctx, UINT32 src, UINT32 opcode)
{ 
    UINT32 dst = RDX, dst2 = RAX;
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(&thread_ctx->vcpu.gpr[src]) || *(&thread_ctx->vcpu.gpr[dst]))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src regs: %u - taints %lu dst regs: %u,%u - taint %lu, %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(&thread_ctx->vcpu.gpr[src]),
                dst, thread_ctx->vcpu.gpr[dst],
                dst2, thread_ctx->vcpu.gpr[dst2]);
#endif
	/* temporary tag value */
	uint64_t tmp_tag = thread_ctx->vcpu.gpr[src] |
        thread_ctx->vcpu.gpr[dst2];

	/* update the destinations */
	thread_ctx->vcpu.gpr[dst] = tmp_tag;
	thread_ctx->vcpu.gpr[dst2] = tmp_tag; 
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src regs: %u - taints %lu dst regs: %u,%u - taint %lu, %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(&thread_ctx->vcpu.gpr[src]),
                dst, thread_ctx->vcpu.gpr[dst],
                dst2, thread_ctx->vcpu.gpr[dst]);
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag among two 8-bit registers
 * and an 8-bit memory location as t[dst] = t[src] | t[AL];
 * dst is AX, whereas src is an 8-bit memory location
 *
 * NOTE: special case for MUL and IMUL instructions
 *
 * @thread_ctx:	the thread context
 * @src:	source memory address
 */
 void PIN_FAST_ANALYSIS_CALL
m2r_mul_opb(thread_ctx_t *thread_ctx, ADDRINT src, UINT32 opcode)
{
    UINT32 dst = AX;
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((uint8_t *)(get_tag_address(src))) || 
            *(((uint16_t *)&thread_ctx->vcpu.gpr[dst])))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint8_t *)(get_tag_address(src))),
                dst, *(((uint16_t *)&thread_ctx->vcpu.gpr[dst])));
#endif

	/* temporary tag value */
	uint8_t tmp_tag = *((uint8_t *)(get_tag_address(src))) |
        *((uint8_t *)&thread_ctx->vcpu.gpr[dst]);

	/* update the destination (ternary) */
	*((uint8_t *)&thread_ctx->vcpu.gpr[dst]) = tmp_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 1) = tmp_tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src: %lx - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint8_t *)(get_tag_address(src))),
                dst, *(((uint16_t *)&thread_ctx->vcpu.gpr[dst])));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag among two 16-bit registers
 * and a 16-bit memory address as
 * t[dst1, dst2] = t[src] | t[dst2]
 *
 * dst1 is DX, dst2 is AX, and src is a 16-bit
 * memory location
 *
 * NOTE: special case for MUL and IMUL instructions
 *
 * @thread_ctx:	the thread context
 * @src:	source memory address
 */
 void PIN_FAST_ANALYSIS_CALL
m2r_mul_opw(thread_ctx_t *thread_ctx, ADDRINT src, UINT32 opcode)
{
    UINT32 dst = DX, dst2 = AX;
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((uint16_t *)(get_tag_address(src))) || 
            *(((uint16_t *)&thread_ctx->vcpu.gpr[dst])) || 
            *(((uint16_t *)&thread_ctx->vcpu.gpr[dst2])))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint 0x%x dst regs: %u,%u - taints %u,%u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint16_t *)(get_tag_address(src))),
                dst, *(((uint16_t *)&thread_ctx->vcpu.gpr[dst])),
                dst2, *(((uint16_t *)&thread_ctx->vcpu.gpr[dst2])));
#endif

	/* temporary tag value */
	uint16_t tmp_tag = *((uint16_t *)(get_tag_address(src))) |
        *((uint16_t *)&thread_ctx->vcpu.gpr[dst]);
	
	/* update the destination (ternary) */
	*((uint16_t *)&thread_ctx->vcpu.gpr[dst])	= tmp_tag;
	*((uint16_t *)&thread_ctx->vcpu.gpr[dst2])	= tmp_tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src: %lx - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint8_t *)(get_tag_address(src))),
                dst, *(((uint16_t *)&thread_ctx->vcpu.gpr[dst])),
                dst2, *(((uint16_t *)&thread_ctx->vcpu.gpr[dst2])));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag among two 32-bit 
 * registers and a 32-bit memory as
 * t[RDX]:t[RAX] = t[src]|t[RAX];
 * src is a memory location
 *
 * NOTE: special case for MUL, IMUL instructions
 *
 * @thread_ctx:	the thread context
 * @src:	source memory address
 */
 void PIN_FAST_ANALYSIS_CALL
m2r_mul_opl(thread_ctx_t *thread_ctx, ADDRINT src, UINT32 opcode)
{
    UINT32 dst = RDX, dst2 = RAX;
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((UINT32 *)(get_tag_address(src))) || 
            thread_ctx->vcpu.gpr[dst] || 
            thread_ctx->vcpu.gpr[dst2])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint 0x%x dst regs: %u,%u - taints %lu,%lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((UINT32 *)(get_tag_address(src))),
                dst, thread_ctx->vcpu.gpr[dst],
                dst2, &thread_ctx->vcpu.gpr[dst2]);
#endif

	/* temporary tag value */
	UINT32 tag = *((UINT32 *)(get_tag_address(src))) | 
        *((UINT32 *)&thread_ctx->vcpu.gpr[dst2]);
	
	/* update the destinations */
	thread_ctx->vcpu.gpr[dst] = tag;
	thread_ctx->vcpu.gpr[dst2] = tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src: %lx - taint 0x%x dst regs: %u,%u - taints %lu,%lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((UINT32 *)(get_tag_address(src))),
                dst, thread_ctx->vcpu.gpr[dst],
                dst2, thread_ctx->vcpu.gpr[dst2]);
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag among two 64-bit 
 * registers and a 64-bit memory as
 * t[RDX]:t[RAX] = t[src]|t[RAX];
 * src is a memory location
 *
 * NOTE: special case for MUL, IMUL instructions
 *
 * @thread_ctx:	the thread context
 * @src:	source memory address
 */
 void PIN_FAST_ANALYSIS_CALL
m2r_mul_opqw(thread_ctx_t *thread_ctx, ADDRINT src, UINT32 opcode)
{
    UINT32 dst = RDX, dst2 = RAX;
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((UINT32 *)(get_tag_address(src))) || 
            thread_ctx->vcpu.gpr[dst] || 
            thread_ctx->vcpu.gpr[dst2])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint 0x%x dst regs: %u,%u - taints %lu,%lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((UINT32 *)(get_tag_address(src))),
                dst, thread_ctx->vcpu.gpr[dst],
                dst2, &thread_ctx->vcpu.gpr[dst2]);
#endif

	/* temporary tag value */
	uint64_t tag = *(ADDRINT *)get_tag_address(src) | 
        *((UINT64 *)&thread_ctx->vcpu.gpr[dst2]);
	
	/* update the destinations */
	thread_ctx->vcpu.gpr[dst] = tag;
	thread_ctx->vcpu.gpr[dst2] = tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src: %lx - taint 0x%x dst regs: %u,%u - taints %lu,%lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((UINT32 *)(get_tag_address(src))),
                dst, thread_ctx->vcpu.gpr[dst],
                dst2, thread_ctx->vcpu.gpr[dst2]);
#endif
}


/*
 * tag propagation (analysis function)
 *
 * propagate tag among three 8-bit registers as t[dst] |= t[upper(src)];
 * dst is AX, whereas src is an upper 8-bit register (e.g., CH, BH, ...)
 *
 * NOTE: special case for DIV and IDIV instructions
 *
 * @thread_ctx:	the thread context
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
r2r_div_opb_u(thread_ctx_t *thread_ctx, UINT32 src, UINT32 opcode)
{
    UINT32 dst = AX;
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1) || *((uint16_t *)&thread_ctx->vcpu.gpr[dst]))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src regs: %u - taints %u dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1),
                dst, *((uint16_t *)&thread_ctx->vcpu.gpr[dst]));
#endif
	/* temporary tag value */
	uint8_t tmp_tag = *(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1) |
        *((uint8_t *)&thread_ctx->vcpu.gpr[dst]) |
        *((uint8_t *)&thread_ctx->vcpu.gpr[dst] + 1);
	
	/* update the destination (ternary) */
	*((uint8_t *)&thread_ctx->vcpu.gpr[dst]) = tmp_tag;
	*((uint8_t *)&thread_ctx->vcpu.gpr[dst] + 1) = tmp_tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src regs: %u - taints %u dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1),
                dst, *((uint16_t *)&thread_ctx->vcpu.gpr[dst]));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag among three 8-bit registers as t[dst] |= t[lower(src)];
 * dst is AX, whereas src is a lower 8-bit register (e.g., CL, BL, ...)
 *
 * NOTE: special case for DIV and IDIV instructions
 *
 * @thread_ctx:	the thread context
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
r2r_div_opb_l(thread_ctx_t *thread_ctx, UINT32 src, UINT32 opcode)
{
    UINT32 dst = AX;
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint8_t *)&thread_ctx->vcpu.gpr[src])) || *((uint16_t *)&thread_ctx->vcpu.gpr[dst]))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src regs: %u - taints %u dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src])),
                dst, *((uint16_t *)&thread_ctx->vcpu.gpr[dst]));
#endif
	/* temporary tag value */
	uint8_t tmp_tag = *((uint8_t *)&thread_ctx->vcpu.gpr[src]) |
            *((uint8_t *)&thread_ctx->vcpu.gpr[dst]) |
            *((uint8_t *)&thread_ctx->vcpu.gpr[dst] + 1);
	
	/* update the destination (ternary) */
	*((uint8_t *)&thread_ctx->vcpu.gpr[dst]) = tmp_tag;
	*((uint8_t *)&thread_ctx->vcpu.gpr[dst] + 1) = tmp_tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src regs: %u - taints %u dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint8_t *)&thread_ctx->vcpu.gpr[src]),
                dst, *((uint16_t *)&thread_ctx->vcpu.gpr[dst]));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between among three 16-bit 
 * registers as t[dst1] |= t[src] and t[dst2] |= t[src];
 * dst1 is DX, dst2 is AX, and src is a 16-bit register 
 * (e.g., CX, BX, ...)
 *
 * NOTE: special case for DIV and IDIV instructions
 *
 * @thread_ctx:	the thread context
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
r2r_div_opw(thread_ctx_t *thread_ctx, UINT32 src, UINT32 opcode)
{
    UINT32 dst = AX, dst2 = DX;
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint16_t *)&thread_ctx->vcpu.gpr[src])) || 
            *((uint16_t *)&thread_ctx->vcpu.gpr[dst]) ||
            *((uint16_t *)&thread_ctx->vcpu.gpr[dst2]))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src regs: %u - taints %u dst regs: %u,%u - taint %u, %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint16_t *)&thread_ctx->vcpu.gpr[src])),
                dst, *((uint16_t *)&thread_ctx->vcpu.gpr[dst]),
                dst2, *((uint16_t *)&thread_ctx->vcpu.gpr[dst2]));
#endif
	/* temporary tag value */
	uint16_t tmp_tag = *((uint16_t *)&thread_ctx->vcpu.gpr[src]) |
        *((uint16_t *)&thread_ctx->vcpu.gpr[dst]) |
        *((uint16_t *)&thread_ctx->vcpu.gpr[dst2]);

	/* update the destination (ternary) */
	*((uint16_t *)&thread_ctx->vcpu.gpr[dst]) = tmp_tag;
	*((uint16_t *)&thread_ctx->vcpu.gpr[dst2]) = tmp_tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src regs: %u - taints %u dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint16_t *)&thread_ctx->vcpu.gpr[src])),
                dst, *((uint16_t *)&thread_ctx->vcpu.gpr[dst]));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between among three 32/64-bit 
 * registers as t[dst1,dst2] = t[src]|t[dst1]|t[dst2] 
 * dst1 is RDX, dst2 is RAX, and src is a 32-bit register
 * (e.g., RCX, RBX, ...)
 *
 * NOTE: special case for DIV and IDIV instructions
 *
 * @thread_ctx:	the thread context
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
r2r_div_opl(thread_ctx_t *thread_ctx, UINT32 src, UINT32 opcode)
{ 
    UINT32 dst = RAX, dst2 = RDX;
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(&thread_ctx->vcpu.gpr[src]) || *(&thread_ctx->vcpu.gpr[dst]))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src regs: %u - taints %lu \
                dst regs: %u,%u - taint %lu, %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(&thread_ctx->vcpu.gpr[src]),
                dst, thread_ctx->vcpu.gpr[dst],
                dst2, thread_ctx->vcpu.gpr[dst2]);
#endif
	/* temporary tag value */
	uint64_t tmp_tag = thread_ctx->vcpu.gpr[src] |
        thread_ctx->vcpu.gpr[dst] |
        thread_ctx->vcpu.gpr[dst];

	/* update the destinations */
	thread_ctx->vcpu.gpr[dst] = tmp_tag;
	thread_ctx->vcpu.gpr[dst2] = tmp_tag; 
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src regs: %u - taints %lu \
                dst regs: %u,%u - taint %lu, %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(&thread_ctx->vcpu.gpr[src]),
                dst, thread_ctx->vcpu.gpr[dst],
                dst2, thread_ctx->vcpu.gpr[dst]);
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag among two 8-bit registers
 * and an 8-bit memory location as t[dst] |= t[src];
 * dst is AX, whereas src is an 8-bit memory location
 *
 * NOTE: special case for DIV and IDIV instructions
 *
 * @thread_ctx:	the thread context
 * @src:	source memory address
 */
 void PIN_FAST_ANALYSIS_CALL
m2r_div_opb(thread_ctx_t *thread_ctx, ADDRINT src, UINT32 opcode)
{
    UINT32 dst = AX;
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((uint8_t *)(get_tag_address(src))) || 
            *(((uint16_t *)&thread_ctx->vcpu.gpr[dst])))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint8_t *)(get_tag_address(src))),
                dst, *(((uint16_t *)&thread_ctx->vcpu.gpr[dst])));
#endif

	/* temporary tag value */
	uint8_t tmp_tag = *((uint8_t *)(get_tag_address(src))) |
        *((uint8_t *)&thread_ctx->vcpu.gpr[dst]) | 
        *((uint8_t *)&thread_ctx->vcpu.gpr[dst] + 1);
	
	/* update the destination (ternary) */
	*((uint8_t *)&thread_ctx->vcpu.gpr[dst]) = tmp_tag;
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 1) = tmp_tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src: %lx - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint8_t *)(get_tag_address(src))),
                dst, *(((uint16_t *)&thread_ctx->vcpu.gpr[dst])));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag among two 16-bit registers
 * and a 16-bit memory address as
 * t[dst1, dst2] = t[src]|t[dst1]|t[dst2]
 *
 * dst1 is DX, dst2 is AX, and src is a 16-bit
 * memory location
 *
 * NOTE: special case for DIV and IDIV instructions
 *
 * @thread_ctx:	the thread context
 * @src:	source memory address
 */
 void PIN_FAST_ANALYSIS_CALL
m2r_div_opw(thread_ctx_t *thread_ctx, ADDRINT src, UINT32 opcode)
{
    UINT32 dst = AX, dst2 = DX;
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((uint16_t *)(get_tag_address(src))) || 
            *(((uint16_t *)&thread_ctx->vcpu.gpr[dst])) || 
            *(((uint16_t *)&thread_ctx->vcpu.gpr[dst2])))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint 0x%x dst regs: %u,%u - taints %u,%u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint16_t *)(get_tag_address(src))),
                dst, *(((uint16_t *)&thread_ctx->vcpu.gpr[dst])),
                dst2, *(((uint16_t *)&thread_ctx->vcpu.gpr[dst2])));
#endif

	/* temporary tag value */
	uint16_t tmp_tag = *((uint16_t *)(get_tag_address(src))) |
        *((uint16_t *)&thread_ctx->vcpu.gpr[dst]) |
        *((uint16_t *)&thread_ctx->vcpu.gpr[dst2]);
	
	/* update the destination (ternary) */
	*((uint16_t *)&thread_ctx->vcpu.gpr[dst])	= tmp_tag;
	*((uint16_t *)&thread_ctx->vcpu.gpr[dst2])	|= tmp_tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src: %lx - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint8_t *)(get_tag_address(src))),
                dst, *(((uint16_t *)&thread_ctx->vcpu.gpr[dst])),
                dst2, *(((uint16_t *)&thread_ctx->vcpu.gpr[dst2])));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag among two 32-bit 
 * registers and a 32-bit memory as
 * t[RDX]:t[RAX] = t[src]|t[RAX]|t[RDX];
 * src is a memory location
 *
 * NOTE: special case for DIV,IDIV instructions
 *
 * @thread_ctx:	the thread context
 * @src:	source memory address
 */
 void PIN_FAST_ANALYSIS_CALL
m2r_div_opl(thread_ctx_t *thread_ctx, ADDRINT src, UINT32 opcode)
{
    UINT32 dst = RDX, dst2 = RAX;
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((UINT32 *)(get_tag_address(src))) || 
            thread_ctx->vcpu.gpr[dst] || 
            thread_ctx->vcpu.gpr[dst2])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint 0x%x dst regs: %u,%u - taints %lu,%lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((UINT32 *)(get_tag_address(src))),
                dst, thread_ctx->vcpu.gpr[dst],
                dst2, &thread_ctx->vcpu.gpr[dst2]);
#endif

	/* temporary tag value */
	UINT32 tag = *((UINT32 *)(get_tag_address(src))) | 
        *((UINT32 *)&thread_ctx->vcpu.gpr[dst]) |
        *((UINT32 *)&thread_ctx->vcpu.gpr[dst2]);
	
	/* update the destinations */
	thread_ctx->vcpu.gpr[dst] = tag;
	thread_ctx->vcpu.gpr[dst2] = tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src: %lx - taint 0x%x dst regs: %u,%u - taints %lu,%lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((UINT32 *)(get_tag_address(src))),
                dst, thread_ctx->vcpu.gpr[dst],
                dst2, thread_ctx->vcpu.gpr[dst2]);
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag among two 64-bit 
 * registers and a 64-bit memory as
 * t[RDX]:t[RAX] = t[src]|t[RAX]|t[RDX];
 * src is a memory location
 *
 * NOTE: special case for DIV,IDIV instructions
 *
 * @thread_ctx:	the thread context
 * @src:	source memory address
 */
 void PIN_FAST_ANALYSIS_CALL
m2r_div_opqw(thread_ctx_t *thread_ctx, ADDRINT src, UINT32 opcode)
{
    UINT32 dst = RDX, dst2 = RAX;
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((UINT32 *)(get_tag_address(src))) || 
            thread_ctx->vcpu.gpr[dst] || 
            thread_ctx->vcpu.gpr[dst2])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint 0x%x dst regs: %u,%u - taints %lu,%lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((UINT32 *)(get_tag_address(src))),
                dst, thread_ctx->vcpu.gpr[dst],
                dst2, &thread_ctx->vcpu.gpr[dst2]);
#endif

	/* temporary tag value */
	uint64_t tag = *(ADDRINT *)get_tag_address(src) | 
        *((UINT64 *)&thread_ctx->vcpu.gpr[dst]) |
        *((UINT64 *)&thread_ctx->vcpu.gpr[dst2]);
	
	/* update the destinations */
	thread_ctx->vcpu.gpr[dst] = tag;
	thread_ctx->vcpu.gpr[dst2] = tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src: %lx - taint 0x%x dst regs: %u,%u - taints %lu,%lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((UINT32 *)(get_tag_address(src))),
                dst, thread_ctx->vcpu.gpr[dst],
                dst2, thread_ctx->vcpu.gpr[dst2]);
#endif
}


/////// GENERIC PROP FUNCTIONS /////////

/*
 * tag propagation (analysis function)
 *
 * propagate tag between two 8-bit 
 * registers as t[upper(dst)] |= t[lower(src)];
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
r2r_binary_opb_ul(thread_ctx_t *thread_ctx, UINT32 dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((uint8_t *)&thread_ctx->vcpu.gpr[src]) || *(((uint8_t *)&thread_ctx->vcpu.gpr[dst])+ 1))
        tainted = 1; 
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint8_t *)&thread_ctx->vcpu.gpr[src]),
                dst, *(((uint8_t *)&thread_ctx->vcpu.gpr[dst])+ 1));
#endif
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 1) |=
		*((uint8_t *)&thread_ctx->vcpu.gpr[src]);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint8_t *)&thread_ctx->vcpu.gpr[src]),
                dst, *(((uint8_t *)&thread_ctx->vcpu.gpr[dst])+ 1));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between two 8-bit 
 * registers as t[lower(dst)] |= t[upper(src)];
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
r2r_binary_opb_lu(thread_ctx_t *thread_ctx, UINT32 dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1) || *((uint8_t *)&thread_ctx->vcpu.gpr[dst]))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1),
                dst, *((uint8_t *)&thread_ctx->vcpu.gpr[dst]));
#endif
	*((uint8_t *)&thread_ctx->vcpu.gpr[dst]) |=
		*(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src])+ 1),
                dst, *(((uint8_t *)&thread_ctx->vcpu.gpr[dst])));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between two 8-bit 
 * registers as t[upper(dst)] |= t[upper(src)]
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
r2r_binary_opb_u(thread_ctx_t *thread_ctx, UINT32 dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if( *(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1) || *(((uint8_t *)&thread_ctx->vcpu.gpr[dst])+ 1))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1),
                dst, *(((uint8_t *)&thread_ctx->vcpu.gpr[dst])+ 1));
#endif
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 1) |=
		*(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1),
                dst, *(((uint8_t *)&thread_ctx->vcpu.gpr[dst])+ 1));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between two 8-bit 
 * registers as t[lower(dst)] |= t[lower(src)]
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
r2r_binary_opb_l(thread_ctx_t *thread_ctx, UINT32 dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint8_t *)&thread_ctx->vcpu.gpr[src])) || *(((uint8_t *)&thread_ctx->vcpu.gpr[dst])))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src])),
                dst, *(((uint8_t *)&thread_ctx->vcpu.gpr[dst])));
#endif
	*((uint8_t *)&thread_ctx->vcpu.gpr[dst]) |=
		*((uint8_t *)&thread_ctx->vcpu.gpr[src]);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src])),
                dst, *(((uint8_t *)&thread_ctx->vcpu.gpr[dst])));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between two 16-bit registers
 * as t[dst] |= t[src]
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
r2r_binary_opw(thread_ctx_t *thread_ctx, UINT32 dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint16_t *)&thread_ctx->vcpu.gpr[src])) || *(((uint16_t *)&thread_ctx->vcpu.gpr[dst])))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint16_t *)&thread_ctx->vcpu.gpr[src])),
                dst, *(((uint16_t *)&thread_ctx->vcpu.gpr[dst])));
#endif
	*((uint16_t *)&thread_ctx->vcpu.gpr[dst]) |=
		*((uint16_t *)&thread_ctx->vcpu.gpr[src]);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint16_t *)&thread_ctx->vcpu.gpr[src])),
                dst, *(((uint16_t *)&thread_ctx->vcpu.gpr[dst])));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between two 32 or 64-bit 
 * registers as t[dst] |= t[src]
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
r2r_binary_opl(thread_ctx_t *thread_ctx, ADDRINT dst, ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((&thread_ctx->vcpu.gpr[src])) || *((&thread_ctx->vcpu.gpr[dst])))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((&thread_ctx->vcpu.gpr[src])),
                dst, *((&thread_ctx->vcpu.gpr[dst])));
#endif
	thread_ctx->vcpu.gpr[dst] |= thread_ctx->vcpu.gpr[src];
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((&thread_ctx->vcpu.gpr[src])),
                dst, *((&thread_ctx->vcpu.gpr[dst])));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between an 8-bit 
 * register and a memory location as
 * t[upper(dst)] |= t[src] (dst is a register)
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source memory address
 */
 void PIN_FAST_ANALYSIS_CALL
m2r_binary_opb_u(thread_ctx_t *thread_ctx, UINT32 dst, ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((uint8_t *)(get_tag_address(src))) || *(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 1))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint8_t *)(get_tag_address(src))),
                dst, *(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 1));
#endif

	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 1) |=
		*((uint8_t *)(get_tag_address(src)));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src: %lx - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint8_t *)(get_tag_address(src))),
                dst, *(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 1));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between an 8-bit 
 * register and a memory location as
 * t[lower(dst)] |= t[src] (dst is a register)
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source memory address
 */
 void PIN_FAST_ANALYSIS_CALL
m2r_binary_opb_l(thread_ctx_t *thread_ctx, UINT32 dst, ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((uint8_t *)(get_tag_address(src))) || *(((uint8_t *)&thread_ctx->vcpu.gpr[dst])))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint8_t *)(get_tag_address(src))),
                dst, *(((uint8_t *)&thread_ctx->vcpu.gpr[dst])));
#endif

	*((uint8_t *)&thread_ctx->vcpu.gpr[dst]) |=
		*((uint8_t *)(get_tag_address(src)));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src: %lx - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint8_t *)(get_tag_address(src))),
                dst, *(((uint8_t *)&thread_ctx->vcpu.gpr[dst])));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between a 16-bit 
 * register and a memory location as
 * t[dst] |= t[src] (dst is a register)
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source memory address
 */
 void PIN_FAST_ANALYSIS_CALL
m2r_binary_opw(thread_ctx_t *thread_ctx, UINT32 dst, ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((uint16_t *)(get_tag_address(src))) || *(((uint16_t *)&thread_ctx->vcpu.gpr[dst])))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint16_t *)(get_tag_address(src))),
                dst, *(((uint16_t *)&thread_ctx->vcpu.gpr[dst])));
#endif

	*((uint16_t *)&thread_ctx->vcpu.gpr[dst]) |=
		*((uint16_t *)(get_tag_address(src)));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src: %lx - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint16_t *)(get_tag_address(src))),
                dst, *(((uint16_t *)&thread_ctx->vcpu.gpr[dst])));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between a 32-bit 
 * register and a memory location as
 * t[dst] |= t[src] (dst is a register)
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source memory address
 */
 void PIN_FAST_ANALYSIS_CALL
m2r_binary_opl(thread_ctx_t *thread_ctx, UINT32 dst, ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((UINT32 *)(get_tag_address(src))) || thread_ctx->vcpu.gpr[dst])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((UINT32 *)(get_tag_address(src))),
                dst, thread_ctx->vcpu.gpr[dst]);
#endif

    m2r_union_32(thread_ctx, dst, src);

#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src: %lx - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((UINT32 *)(get_tag_address(src))),
                dst, *(((UINT32 *)&thread_ctx->vcpu.gpr[dst])));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between a 64-bit 
 * register and a memory location as
 * t[dst] |= t[src] (dst is a register)
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source memory address
 */
 void PIN_FAST_ANALYSIS_CALL
m2r_binary_opqw(thread_ctx_t *thread_ctx, UINT32 dst, ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(ADDRINT *)(get_tag_address(src)) || thread_ctx->vcpu.gpr[dst])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(ADDRINT *)(get_tag_address(src)),
                dst, thread_ctx->vcpu.gpr[dst]);
#endif

	thread_ctx->vcpu.gpr[dst] |= *(ADDRINT *)(get_tag_address(src));

#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src: %lx - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(ADDRINT *)(get_tag_address(src)),
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between an 8-bit 
 * register and a memory location as
 * t[dst] |= t[upper(src)] (src is a register)
 *
 * @thread_ctx:	the thread context
 * @dst:	destination memory address
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
r2m_binary_opb_u(thread_ctx_t *thread_ctx, ADDRINT dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1) || *((uint8_t *)(get_tag_address(dst))))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1),
                dst, *((uint8_t *)(get_tag_address(dst))));
#endif
	*((uint8_t *)(get_tag_address(dst))) |= 
		*(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1),
                dst, *((uint8_t *)(get_tag_address(dst))));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between an 8-bit 
 * register and a memory location as
 * t[dst] |= t[lower(src)] (src is a register)
 *
 * @thread_ctx:	the thread context
 * @dst:	destination memory address
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
r2m_binary_opb_l(thread_ctx_t *thread_ctx, ADDRINT dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint8_t *)&thread_ctx->vcpu.gpr[src])) || *((uint8_t *)(get_tag_address(dst))))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src])),
                dst, *((uint8_t *)(get_tag_address(dst))));
#endif
	*((uint8_t *)(get_tag_address(dst))) |= 
		*((uint8_t *)&thread_ctx->vcpu.gpr[src]);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src])),
                dst, *((uint8_t *)(get_tag_address(dst))));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between a 16-bit 
 * register and a memory location as
 * t[dst] |= t[src] (src is a register)
 *
 * @thread_ctx:	the thread context
 * @dst:	destination memory address
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
r2m_binary_opw(thread_ctx_t *thread_ctx, ADDRINT dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint16_t *)&thread_ctx->vcpu.gpr[src])) || *((uint16_t *)(get_tag_address(dst))))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint16_t *)&thread_ctx->vcpu.gpr[src])),
                dst, *((uint16_t *)(get_tag_address(dst))));
#endif
	*((uint16_t *)(get_tag_address(dst))) |= 
		*((uint16_t *)&thread_ctx->vcpu.gpr[src]);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint16_t *)&thread_ctx->vcpu.gpr[src])),
                dst, *((uint16_t *)(get_tag_address(dst))));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between a 32-bit 
 * register and a memory location as
 * t[dst] |= t[src] (src is a register)
 *
 * @thread_ctx:	the thread context
 * @dst:	destination memory address
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
r2m_binary_opl(thread_ctx_t *thread_ctx, ADDRINT dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.gpr[src] || *((UINT32 *)(get_tag_address(dst))))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, thread_ctx->vcpu.gpr[src],
                dst, *((UINT32 *)(get_tag_address(dst))));
#endif
	*((UINT32 *)(get_tag_address(dst))) |=
		(UINT32)thread_ctx->vcpu.gpr[src];
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, thread_ctx->vcpu.gpr[src],
                dst, *((UINT32 *)(get_tag_address(dst))));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between a 64-bit 
 * register and a memory location as
 * t[dst] |= t[src] (src is a register)
 *
 * @thread_ctx:	the thread context
 * @dst:	destination memory address
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
r2m_binary_opqw(thread_ctx_t *thread_ctx, ADDRINT dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.gpr[src] || *(ADDRINT *)(get_tag_address(dst)))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, thread_ctx->vcpu.gpr[src],
                dst, *(ADDRINT *)(get_tag_address(dst)));
#endif
	*(ADDRINT *)(get_tag_address(dst)) |= thread_ctx->vcpu.gpr[src];
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, thread_ctx->vcpu.gpr[src],
                dst, *(ADDRINT *)(get_tag_address(dst)));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * clear the tag of RAX, RBX, RCX, RDX
 * INS: CPUID
 *
 * @thread_ctx:	the thread context
 * @reg:	register index (VCPU) 
 */
 void PIN_FAST_ANALYSIS_CALL
r_clrl4(thread_ctx_t *thread_ctx, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.gpr[RAX] || thread_ctx->vcpu.gpr[RBX] || 
            thread_ctx->vcpu.gpr[RCX] || thread_ctx->vcpu.gpr[RDX] )
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src regs: %u %u %u %u- taint %lu %lu %lu %lu %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                RAX, thread_ctx->vcpu.gpr[RAX],
                RBX, thread_ctx->vcpu.gpr[RBX], 
                RCX, thread_ctx->vcpu.gpr[RCX],
                RDX, thread_ctx->vcpu.gpr[RDX]);
#endif
	thread_ctx->vcpu.gpr[RAX] = TAG_ZERO;
	thread_ctx->vcpu.gpr[RBX] = TAG_ZERO;
	thread_ctx->vcpu.gpr[RCX] = TAG_ZERO;
	thread_ctx->vcpu.gpr[RDX] = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s clear regs: %u %u %u %u- taint 0x%x %u %u %u %u\n",
                OPCODE_StringShort(opcode).c_str(),
                RAX, thread_ctx->vcpu.gpr[RAX],
                RBX, thread_ctx->vcpu.gpr[RBX], 
                RCX, thread_ctx->vcpu.gpr[RCX],
                RDX, thread_ctx->vcpu.gpr[RDX]);
#endif
}

/*
 * tag propagation (analysis function)
 *
 * clear the tag of RAX, RDX
 *
 * @thread_ctx:	the thread context
 * @reg:	register index (VCPU) 
 */
 void PIN_FAST_ANALYSIS_CALL
r_clrl2(thread_ctx_t *thread_ctx, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.gpr[RAX] || thread_ctx->vcpu.gpr[RDX])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src regs: %u %u- taint %lu %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                RAX, thread_ctx->vcpu.gpr[RAX], 
                RDX, thread_ctx->vcpu.gpr[RDX]);
#endif
	thread_ctx->vcpu.gpr[RAX] = TAG_ZERO;
	thread_ctx->vcpu.gpr[RDX] = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s cleared regs: %u %u- taint %lu %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                RAX, thread_ctx->vcpu.gpr[RAX], 
                RDX, thread_ctx->vcpu.gpr[RDX]);
#endif
}


/*
 * tag propagation (analysis function)
 *
 * clear the tag of a 32 or 64-bit register. Since 32-bit register 
 * operands zero the upper 32-bits, we can treat them the same.
 *
 * @thread_ctx:	the thread context
 * @reg:	register index (VCPU) 
 */
 void PIN_FAST_ANALYSIS_CALL
r_clrl(thread_ctx_t *thread_ctx, UINT32 reg, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.gpr[reg])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u- taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                reg, thread_ctx->vcpu.gpr[reg]);
#endif
	thread_ctx->vcpu.gpr[reg] = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s cleared reg: %u- taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                reg, thread_ctx->vcpu.gpr[reg]);
#endif
}

/*
 * tag propagation (analysis function)
 *
 * clear the tag of a 16-bit register
 *
 * @thread_ctx:	the thread context
 * @reg:	register index (VCPU) 
 */
 void PIN_FAST_ANALYSIS_CALL
r_clrw(thread_ctx_t *thread_ctx, UINT32 reg, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((uint16_t *)&thread_ctx->vcpu.gpr[reg]))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u- taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                reg, *((uint16_t *)&thread_ctx->vcpu.gpr[reg]));
#endif
	*((uint16_t *)&thread_ctx->vcpu.gpr[reg]) = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s cleared reg: %u- taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                reg, *((uint16_t *)&thread_ctx->vcpu.gpr[reg]));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * clear the tag of an upper 8-bit register
 *
 * @thread_ctx:	the thread context
 * @reg:	register index (VCPU) 
 */
 void PIN_FAST_ANALYSIS_CALL
r_clrb_u(thread_ctx_t *thread_ctx, UINT32 reg, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint8_t *)&thread_ctx->vcpu.gpr[reg]) + 1))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u- taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                reg, *(((uint8_t *)&thread_ctx->vcpu.gpr[reg]) + 1));
#endif
	*(((uint8_t *)&thread_ctx->vcpu.gpr[reg]) + 1) = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s cleared reg: %u- taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                reg, *(((uint8_t *)&thread_ctx->vcpu.gpr[reg]) + 1));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * clear the tag of a lower 8-bit register
 *
 * @thread_ctx:	the thread context
 * @reg:	register index (VCPU) 
 */
 void PIN_FAST_ANALYSIS_CALL
r_clrb_l(thread_ctx_t *thread_ctx, UINT32 reg, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((uint8_t *)&thread_ctx->vcpu.gpr[reg]))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u- taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                reg, *((uint8_t *)&thread_ctx->vcpu.gpr[reg]));
#endif
	*((uint8_t *)&thread_ctx->vcpu.gpr[reg]) = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s cleared reg: %u- taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                reg, *((uint8_t *)&thread_ctx->vcpu.gpr[reg]));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between two 8-bit 
 * registers as t[upper(dst)] = t[lower(src)]
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
r2r_xfer_opb_ul(thread_ctx_t *thread_ctx, UINT32 dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((uint8_t *)&thread_ctx->vcpu.gpr[src]) || *(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 1))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src])),
                dst, *(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 1));
#endif
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 1) =
		*((uint8_t *)&thread_ctx->vcpu.gpr[src]);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src])),
                dst, *(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 1));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between two 8-bit 
 * registers as t[lower(dst)] = t[upper(src)];
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
r2r_xfer_opb_lu(thread_ctx_t *thread_ctx, UINT32 dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1) || *(((uint8_t *)&thread_ctx->vcpu.gpr[dst])))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1),
                dst, *(((uint8_t *)&thread_ctx->vcpu.gpr[dst])));
#endif
	*((uint8_t *)&thread_ctx->vcpu.gpr[dst]) =
		*(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1),
                dst, *(((uint8_t *)&thread_ctx->vcpu.gpr[dst])));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between two 8-bit 
 * registers as t[upper(dst)] = t[upper(src)]
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
r2r_xfer_opb_u(thread_ctx_t *thread_ctx, UINT32 dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1) || *(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 1))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1),
                dst, *(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 1));
#endif
	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 1) =
		*(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1),
                dst, *(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 1));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between two 8-bit 
 * registers as t[lower(dst)] = t[lower(src)]
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
r2r_xfer_opb_l(thread_ctx_t *thread_ctx, UINT32 dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint8_t *)&thread_ctx->vcpu.gpr[src])) || *(((uint8_t *)&thread_ctx->vcpu.gpr[dst])))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src])),
                dst, *(((uint8_t *)&thread_ctx->vcpu.gpr[dst])));
#endif
	*((uint8_t *)&thread_ctx->vcpu.gpr[dst]) =
		*((uint8_t *)&thread_ctx->vcpu.gpr[src]);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src])),
                dst, *(((uint8_t *)&thread_ctx->vcpu.gpr[dst])));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between two 16-bit 
 * registers as t[dst] = t[src]
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
r2r_xfer_opw(thread_ctx_t *thread_ctx, UINT32 dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint16_t *)&thread_ctx->vcpu.gpr[src])) || *(((uint16_t *)&thread_ctx->vcpu.gpr[dst])))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint16_t *)&thread_ctx->vcpu.gpr[src])),
                dst, *(((uint16_t *)&thread_ctx->vcpu.gpr[dst])));
#endif
	*((uint16_t *)&thread_ctx->vcpu.gpr[dst]) =
		*((uint16_t *)&thread_ctx->vcpu.gpr[src]);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint16_t *)&thread_ctx->vcpu.gpr[src])),
                dst, *(((uint16_t *)&thread_ctx->vcpu.gpr[dst])));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between two 32 or 64-bit 
 * registers as t[dst] = t[src]
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
r2r_xfer_opl(thread_ctx_t *thread_ctx, UINT32 dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.gpr[src] || *((&thread_ctx->vcpu.gpr[dst])))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((&thread_ctx->vcpu.gpr[src])),
                dst, *((&thread_ctx->vcpu.gpr[dst])));
#endif
	thread_ctx->vcpu.gpr[dst] = thread_ctx->vcpu.gpr[src];
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((&thread_ctx->vcpu.gpr[src])),
                dst, *((&thread_ctx->vcpu.gpr[dst])));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between an upper 8-bit 
 * register and a memory location as
 * t[dst] = t[src] (dst is a register)
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source memory address
 */
 void PIN_FAST_ANALYSIS_CALL
m2r_xfer_opb_u(thread_ctx_t *thread_ctx, UINT32 dst, ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((uint8_t *)(get_tag_address(src))) || *(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 1))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint8_t *)(get_tag_address(src))),
                dst, *(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 1));
#endif

	*(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 1) =
		*((uint8_t *)(get_tag_address(src)));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src: %lx - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint8_t *)(get_tag_address(src))),
                dst, *(((uint8_t *)&thread_ctx->vcpu.gpr[dst]) + 1));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between a lower 8-bit 
 * register and a memory location as
 * t[dst] = t[src] (dst is a register)
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source memory address
 */
 void PIN_FAST_ANALYSIS_CALL
m2r_xfer_opb_l(thread_ctx_t *thread_ctx, UINT32 dst, ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((uint8_t *)(get_tag_address(src))) || *(((uint8_t *)&thread_ctx->vcpu.gpr[dst])))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint8_t *)(get_tag_address(src))),
                dst, *(((uint8_t *)&thread_ctx->vcpu.gpr[dst])));
#endif

	*((uint8_t *)&thread_ctx->vcpu.gpr[dst]) =
		*((uint8_t *)(get_tag_address(src)));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src: %lx - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint8_t *)(get_tag_address(src))),
                dst, *(((uint8_t *)&thread_ctx->vcpu.gpr[dst])));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between a 16-bit 
 * register and a memory location as
 * t[dst] = t[src] (dst is a register)
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source memory address
 */
 void PIN_FAST_ANALYSIS_CALL
m2r_xfer_opw(thread_ctx_t *thread_ctx, UINT32 dst, ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((uint16_t *)(get_tag_address(src))) || *(((uint16_t *)&thread_ctx->vcpu.gpr[dst])))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint16_t *)(get_tag_address(src))),
                dst, *(((uint16_t *)&thread_ctx->vcpu.gpr[dst])));
#endif

	*((uint16_t *)&thread_ctx->vcpu.gpr[dst]) =
		*((uint16_t *)(get_tag_address(src)));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src: %lx - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint16_t *)(get_tag_address(src))),
                dst, *(((uint16_t *)&thread_ctx->vcpu.gpr[dst])));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between a 32-bit 
 * register and a memory location as
 * t[dst] = t[src] (dst is a register)
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source memory address
 */
 void PIN_FAST_ANALYSIS_CALL
m2r_xfer_opl(thread_ctx_t *thread_ctx, UINT32 dst, ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((UINT32 *)(get_tag_address(src))) || thread_ctx->vcpu.gpr[dst])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((UINT32 *)(get_tag_address(src))),
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
    m2r_mov_32(thread_ctx, dst, src);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src: %lx - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((UINT32 *)(get_tag_address(src))),
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between a 64-bit 
 * register and a memory location as
 * t[dst] = t[src] (dst is a register)
 *
 * @thread_ctx:	the thread context
 * @dst:	destination register index (VCPU)
 * @src:	source memory address
 */
 void PIN_FAST_ANALYSIS_CALL
m2r_xfer_opqw(thread_ctx_t *thread_ctx, UINT32 dst, ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
     if(*(ADDRINT *)get_tag_address(src) || thread_ctx->vcpu.gpr[dst])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(ADDRINT *)get_tag_address(src),
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
    thread_ctx->vcpu.gpr[dst] = *(ADDRINT *)get_tag_address(src);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src: %lx - taint 0x%x dst reg: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(ADDRINT *)get_tag_address(src),
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
}

//#if 1
/*
 * tag propagation (analysis function)
 *
 * propagate tag between an 8-bit 
 * register and a n-memory locations as
 * t[dst] = t[src]; src is AL
 *
 * @thread_ctx:	the thread context
 * @dst:	destination memory address
 * @count:	memory bytes
 * @eflags:	the value of the EFLAGS register
 */
 void PIN_FAST_ANALYSIS_CALL
r2m_xfer_opbn(thread_ctx_t *thread_ctx,
		ADDRINT dst,
		UINT32 count,
		UINT32 eflags, UINT32 opcode)
{
    UINT32 src = RAX;
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint8_t *)&thread_ctx->vcpu.gpr[src])) || mem_is_tainted(dst, count))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x dst: %lx num: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src])),
                dst, count, mem_is_tainted(dst, count));
#endif
	if (likely(EFLAGS_DF(eflags) == 0))
		/* EFLAGS.DF = 0 */
		(void)memset((void *)(get_tag_address(dst)),
			thread_ctx->vcpu.gpr[src], count);
	else
		/* EFLAGS.DF = 1 */
		(void)memset((void *)(get_tag_address(dst) - count + 1),
			thread_ctx->vcpu.gpr[src], count);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x dst: %lx num: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src])),
                dst, count, mem_is_tainted(dst, count));
#endif
}
//#endif

/*
 * tag propagation (analysis function)
 *
 * propagate tag between an 8-bit 
 * register and a memory location as
 * t[dst] = t[upper(src)] (src is a register)
 *
 * @thread_ctx:	the thread context
 * @dst:	destination memory address
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
r2m_xfer_opb_u(thread_ctx_t *thread_ctx, ADDRINT dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1) || *((uint8_t *)(get_tag_address(dst))))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1),
                dst, *((uint8_t *)(get_tag_address(dst))));
#endif
	*((uint8_t *)(get_tag_address(dst))) =
		*(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src]) + 1),
                dst, *((uint8_t *)(get_tag_address(dst))));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between an 8-bit 
 * register and a memory location as
 * t[dst] = t[lower(src)] (src is a register)
 *
 * @thread_ctx:	the thread context
 * @dst:	destination memory address
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
r2m_xfer_opb_l(thread_ctx_t *thread_ctx, ADDRINT dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint8_t *)&thread_ctx->vcpu.gpr[src])) || *((uint8_t *)(get_tag_address(dst))))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src])),
                dst, *((uint8_t *)(get_tag_address(dst))));
#endif
	*((uint8_t *)(get_tag_address(dst))) =
		*((uint8_t *)&thread_ctx->vcpu.gpr[src]);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint8_t *)&thread_ctx->vcpu.gpr[src])),
                dst, *((uint8_t *)(get_tag_address(dst))));
#endif
}

#if 0
/*
 * tag propagation (analysis function)
 *
 * propagate tag between a 16-bit 
 * register and a n-memory locations as
 * t[dst] = t[src]; src is AX
 *
 * @thread_ctx:	the thread context
 * @dst:	destination memory address
 * @count:	memory words
 * @eflags:	the value of the EFLAGS register
 */
 void PIN_FAST_ANALYSIS_CALL
r2m_xfer_opwn(thread_ctx_t *thread_ctx,
		ADDRINT dst,
		UINT32 count,
		UINT32 eflags, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    UINT32 src = RAX;
    if(*(((uint16_t *)&thread_ctx->vcpu.gpr[src])) || mem_is_tainted(dst, count * 2))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x dst: %lx num words: %d- taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint16_t *)&thread_ctx->vcpu.gpr[src])),
                dst, count, mem_is_tainted(dst, count<<1));
#endif
	/* temporaries */
	UINT32 tmp_tag	= *((uint16_t *)&thread_ctx->vcpu.gpr[RAX]);
	UINT32 addr		= *(ADDRINT *)get_tag_address(dst);

	/* extend the value of tmp_tag */
	tmp_tag |= (tmp_tag << 16);
		
	/* count is odd */
	if ((count != 0) && (count % 2 != 0)) {
		if (likely(EFLAGS_DF(eflags) == 0)) {
			/* EFLAGS.DF = 0 */
			/* fast path */
			(void)wmemset((wchar_t *)addr, (wchar_t)tmp_tag,
				(count - 1) >> 1);

			/* remainder */
			*(uint16_t *)(addr + (count << 1) - 2) =
				(uint16_t)tmp_tag;
		}
		else {
			/* EFLAGS.DF = 1 */
			/* fast path */
			(void)wmemset((wchar_t *) (addr - (count << 1) + 3),
					(wchar_t)tmp_tag, (count - 1) >> 1);

			/* remainder */
			*(uint16_t *)(addr - (count << 1) + 1) =
				(uint16_t)tmp_tag;
		}
	}
	/* count is even */
	else {

		if (likely(EFLAGS_DF(eflags) == 0 || count == 0))
			/* EFLAGS.DF = 0 */
			(void)wmemset((wchar_t *)addr,
					(wchar_t)tmp_tag,
					count >> 1);
		else
			/* EFLAGS.DF = 1 */
			(void)wmemset((wchar_t *)(addr - (count << 1) + 1),
					(wchar_t)tmp_tag,
					count >> 1);
	}
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x dst: %lx num words: %d- taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint16_t *)&thread_ctx->vcpu.gpr[src])),
                dst, count, mem_is_tainted(dst, count<<1));
#endif
}
#endif

/*
 * tag propagation (analysis function)
 *
 * propagate tag between a 16-bit 
 * register and a memory location as
 * t[dst] = t[src] (src is a register)
 *
 * @thread_ctx:	the thread context
 * @dst:	destination memory address
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
r2m_xfer_opw(thread_ctx_t *thread_ctx, ADDRINT dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint16_t *)&thread_ctx->vcpu.gpr[src])) || *((uint16_t *)(get_tag_address(dst))))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint16_t *)&thread_ctx->vcpu.gpr[src])),
                dst, *((uint16_t *)(get_tag_address(dst))));
#endif
	*((uint16_t *)(get_tag_address(dst))) =
		*((uint16_t *)&thread_ctx->vcpu.gpr[src]);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((uint16_t *)&thread_ctx->vcpu.gpr[src])),
                dst, *((uint16_t *)(get_tag_address(dst))));
#endif
}
#if 0
/*
 * tag propagation (analysis function)
 *
 * propagate tag between a 32-bit 
 * register and a n-memory locations as
 * t[dst] = t[src]; src is RAX
 *
 * @thread_ctx:	the thread context
 * @dst:	destination memory address
 * @src:	source register index (VCPU)
 * @count:	memory double words
 * @eflags:	the value of the EFLAGS register
 */
 void PIN_FAST_ANALYSIS_CALL
r2m_xfer_opln(thread_ctx_t *thread_ctx,
		ADDRINT dst,
		UINT32 count,
		UINT32 eflags, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG

    int tainted = 0;
    UINT32 src = RAX;
    if(*(((UINT32 *)&thread_ctx->vcpu.gpr[src])) || mem_is_tainted(dst, count<<2))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x dst: %lx num dwords: %d - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((UINT32 *)&thread_ctx->vcpu.gpr[src])),
                dst, count, mem_is_tainted(dst, count<<2));
#endif
	if (likely(EFLAGS_DF(eflags) == 0))
		/* EFLAGS.DF = 0 */
		(void)memset((wchar_t *)(get_tag_address(dst)),
			(wchar_t)thread_ctx->vcpu.gpr[src], count);
	else
		/* EFLAGS.DF = 1 */
		(void)wmemset((wchar_t *)
			(get_tag_address(dst) - (count << 2) + 1),
				(wchar_t)thread_ctx->vcpu.gpr[src], count);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x \
                dst: %lx num dwords: %d - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((UINT32 *)&thread_ctx->vcpu.gpr[src])),
                dst, count, mem_is_tainted(dst, count<<2));
#endif
}
#endif
#if 0
/*
 * tag propagation (analysis function)
 *
 * propagate tag between a 64-bit 
 * register and a n-memory locations as
 * t[dst] = t[src]; src is RAX
 *
 * @thread_ctx:	the thread context
 * @dst:	destination memory address
 * @src:	source register index (VCPU)
 * @count:	memory double words
 * @eflags:	the value of the EFLAGS register
 */
 void PIN_FAST_ANALYSIS_CALL
r2m_xfer_opqwn(thread_ctx_t *thread_ctx,
		ADDRINT dst,
		UINT32 count,
		UINT32 eflags, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG

    int tainted = 0;
    UINT32 src = RAX;
    if(thread_ctx->vcpu.gpr[src] || mem_is_tainted(dst, count << 3))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x \
                dst: %lx num dwords: %d - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((UINT32 *)&thread_ctx->vcpu.gpr[src])),
                dst, count, mem_is_tainted(dst, count << 3));
#endif
    //TODO: optimize this?
	if (likely(EFLAGS_DF(eflags) == 0))
		/* EFLAGS.DF = 0 */
        for (int i = 0; i < count << 3; i += 1<<3)
            *(dst + i + *(ADDRINT *)get_tag_address(dst + i)) = thread_ctx->vcpu.gpr[src];
        /*    
		(void)wmemset((wchar_t *)(get_tag_address(dst)),
			(wchar_t)thread_ctx->vcpu.gpr[src], count);
        */
	else
		/* EFLAGS.DF = 1 */
        for (int i = count << 3; i > 0; i -= 1<<3)
            *(dst + i + get_tag_address(dst + i)) = thread_ctx->vcpu.gpr[src];

        /*
		(void)wmemset((wchar_t *)
			(get_tag_address(dst) - (count << 2) + 1),
				(wchar_t)thread_ctx->vcpu.gpr[src], count);
        */
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x \
                dst: %lx num dwords: %d - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, thread_ctx->vcpu.gpr[src],
                dst, count, mem_is_tainted(dst, count << 3));
#endif
}
#endif


/*
 * tag propagation (analysis function)
 *
 * propagate tag between a 64-bit 
 * register and a memory location as
 * t[dst] = t[src] (src is a register)
 *
 * @thread_ctx:	the thread context
 * @dst:	destination memory address
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
r2m_xfer_opqw(thread_ctx_t *thread_ctx, ADDRINT dst, UINT32 src, 
        UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.gpr[src] || *(ADDRINT *)(get_tag_address(dst)))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, thread_ctx->vcpu.gpr[src],
                dst, *(ADDRINT *)(get_tag_address(dst)));
#endif
	*(ADDRINT *)(get_tag_address(dst)) = thread_ctx->vcpu.gpr[src];
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, thread_ctx->vcpu.gpr[src],
                dst, *(ADDRINT *)(get_tag_address(dst)));
#endif
}


/*
 * tag propagation (analysis function)
 *
 * propagate tag between a 32-bit 
 * register and a memory location as
 * t[dst] = t[src] (src is a register)
 *
 * @thread_ctx:	the thread context
 * @dst:	destination memory address
 * @src:	source register index (VCPU)
 */
 void PIN_FAST_ANALYSIS_CALL
r2m_xfer_opl(thread_ctx_t *thread_ctx, ADDRINT dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((UINT32 *)&thread_ctx->vcpu.gpr[src]) || 
            *((UINT32 *)get_tag_address(dst)))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg: %u - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((UINT32 *)&thread_ctx->vcpu.gpr[src])),
                dst, *((UINT32 *)(get_tag_address(dst))));
#endif
	*((UINT32 *)get_tag_address(dst)) =
		*((UINT32 *)&thread_ctx->vcpu.gpr[src]);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg: %u - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((UINT32 *)&thread_ctx->vcpu.gpr[src])),
                dst, *((UINT32 *)(get_tag_address(dst))));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between two 16-bit 
 * memory locations as t[dst] = t[src]
 *
 * @dst:	destination memory address
 * @src:	source memory address
 */
 void PIN_FAST_ANALYSIS_CALL
m2m_xfer_opw(ADDRINT dst, ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((uint16_t *)(get_tag_address(src))) || *((uint16_t *)(get_tag_address(dst))))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint16_t *)(get_tag_address(src))),
                dst, *((uint16_t *)(get_tag_address(dst))));
#endif

	*((uint16_t *)(get_tag_address(dst))) =
		*((uint16_t *)(get_tag_address(src)));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src: %lx - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint16_t *)(get_tag_address(src))),
                dst, *((uint16_t *)(get_tag_address(dst))));
#endif
	
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between two 8-bit 
 * memory locations as t[dst] = t[src]
 *
 * @dst:	destination memory address
 * @src:	source memory address
 */
 void PIN_FAST_ANALYSIS_CALL
m2m_xfer_opb(ADDRINT dst, ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((uint8_t *)(get_tag_address(src))) || *((uint8_t *)(get_tag_address(dst))))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint8_t *)(get_tag_address(src))),
                dst, *((uint8_t *)(get_tag_address(dst))));
#endif

	*((uint8_t *)(get_tag_address(dst))) =
		*((uint8_t *)(get_tag_address(src)));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src: %lx - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint8_t *)(get_tag_address(src))),
                dst, *((uint8_t *)(get_tag_address(dst))));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between two 32-bit 
 * memory locations as t[dst] = t[src]
 *
 * @dst:	destination memory address
 * @src:	source memory address
 */
 void PIN_FAST_ANALYSIS_CALL
m2m_xfer_opl(ADDRINT dst, ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((UINT32 *)(get_tag_address(src))) || *((UINT32 *)(get_tag_address(dst))))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((UINT32 *)(get_tag_address(src))),
                dst, *((UINT32 *)(get_tag_address(dst))));
#endif

	*((UINT32 *)(get_tag_address(dst))) =
		*((UINT32 *)(get_tag_address(src)));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src: %lx - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((UINT32 *)(get_tag_address(src))),
                dst, *((UINT32 *)(get_tag_address(dst))));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between two 64-bit 
 * memory locations as t[dst] = t[src]
 *
 * @dst:	destination memory address
 * @src:	source memory address
 */
 void PIN_FAST_ANALYSIS_CALL
m2m_xfer_opqw(ADDRINT dst, ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(ADDRINT *)(get_tag_address(src)) || *(ADDRINT *)(get_tag_address(dst)))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(ADDRINT *)(get_tag_address(src)),
                dst, *(ADDRINT *)(get_tag_address(dst)));
#endif

	*(ADDRINT *)(get_tag_address(dst)) =
		*(ADDRINT *)(get_tag_address(src));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src: %lx - taint 0x%x dst: %lx - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(ADDRINT *)(get_tag_address(src)),
                dst, *(ADDRINT *)(get_tag_address(dst)));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between n 16-bit 
 * memory locations as t[dst] = t[src]
 *
 * @dst:	destination memory address
 * @src:	source memory address
 * @count:	memory words
 * @eflags:	the value of the EFLAGS register
 */
 void PIN_FAST_ANALYSIS_CALL
m2m_xfer_opwn(ADDRINT dst, ADDRINT src, ADDRINT count, ADDRINT eflags, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((uint16_t *)(get_tag_address(src))) || mem_is_tainted(dst, count<<1))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint 0x%x dst: %lx num words: %d - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint16_t *)(get_tag_address(src))),
                dst, count, mem_is_tainted(dst, 2*count));
#endif

	if (likely(EFLAGS_DF(eflags) == 0))
		/* EFLAGS.DF = 0 */
		(void)memcpy((void *)(get_tag_address(dst)),
			(void *)(get_tag_address(src)),
			count << 1);
	else
		/* EFLAGS.DF = 1 */
		(void)memcpy((void *)
			(get_tag_address(dst) - (count << 1) + 1),
			(void *)(get_tag_address(src) - (count << 1) + 1),
			count << 1);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src: %lx - taint 0x%x dst: %lx num words: %d - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint16_t *)(get_tag_address(src))),
                dst, count, mem_is_tainted(dst, count<<1));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between n 8-bit 
 * memory locations as t[dst] = t[src]
 *
 * @dst:	destination memory address
 * @src:	source memory address
 * @count:	memory bytes
 * @eflags:	the value of the EFLAGS register
 */
 void PIN_FAST_ANALYSIS_CALL
m2m_xfer_opbn(ADDRINT dst, ADDRINT src, ADDRINT count, 
        ADDRINT eflags, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((uint8_t *)(get_tag_address(src))) || mem_is_tainted(dst, count))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint 0x%x dst: %lx num bytes: %d - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint8_t *)(get_tag_address(src))),
                dst, count, mem_is_tainted(dst, count));
#endif

	if (likely(EFLAGS_DF(eflags) == 0))
		/* EFLAGS.DF = 0 */
		(void)memcpy((void *)(get_tag_address(dst)),
			(void *)(get_tag_address(src)),
			count);
	else
		/* EFLAGS.DF = 1 */
		(void)memcpy((void *)(get_tag_address(dst) - count + 1),
			(void *)(get_tag_address(src) - count + 1),
			count);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src: %lx - taint 0x%x dst: %lx num bytes: %d - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint8_t *)(get_tag_address(src))),
                dst, count, mem_is_tainted(dst, count));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between n 32-bit 
 * memory locations as t[dst] = t[src]
 *
 * @dst:	destination memory address
 * @src:	source memory address
 * @count:	memory double words
 * @eflags:	the value of the EFLAGS register
 */
 void PIN_FAST_ANALYSIS_CALL
m2m_xfer_opln(ADDRINT dst, ADDRINT src, ADDRINT count, 
        ADDRINT eflags, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((UINT32 *)(get_tag_address(src))) ||  
            mem_is_tainted(dst, count << 2))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint 0x%x dst: %lx num dwords: %d - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((UINT32 *)(get_tag_address(src))),
                dst, count, mem_is_tainted(dst, count << 2));
#endif

	if (likely(EFLAGS_DF(eflags) == 0))
		/* EFLAGS.DF = 0 */
		(void)memcpy((void *)(get_tag_address(dst)),
			(const void *)get_tag_address(src), count << 2);
	else
		/* EFLAGS.DF = 1 */
		(void)memcpy((void *)
			(get_tag_address(dst) - (count << 2) + 1),
			(void *)(get_tag_address(src) - (count << 2) + 1),
			count << 2);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src: %lx - taint 0x%x dst: %lx num dwords: %d - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((UINT32 *)(get_tag_address(src))),
                dst, count, mem_is_tainted(dst, count<<2));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * propagate tag between n 64-bit 
 * memory locations as t[dst] = t[src]
 *
 * @dst:	destination memory address
 * @src:	source memory address
 * @count:	memory double words
 * @eflags:	the value of the EFLAGS register
 */
 void PIN_FAST_ANALYSIS_CALL
m2m_xfer_opqwn(ADDRINT dst, ADDRINT src, 
        ADDRINT count, ADDRINT eflags, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(mem_is_tainted(get_tag_address(src), count << 3) ||  
            mem_is_tainted(dst, count << 3))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint 0x%x dst: %lx \
                num qwords: %d - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, mem_is_tainted(get_tag_address(src), count << 3),
                dst, count, mem_is_tainted(dst, count << 3));
#endif

	if (likely(EFLAGS_DF(eflags) == 0))
		/* EFLAGS.DF = 0 */
		(void)memcpy((void *)(get_tag_address(dst)),
			(void *)(get_tag_address(src)),
			count << 3);
	else
		/* EFLAGS.DF = 1 */
		(void)memcpy((void *)
			(get_tag_address(dst) - (count << 3) + 1),
			(void *)(get_tag_address(src) - (count << 3) + 1),
			count << 3);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src: %lx - taint 0x%x dst: %lx num qwords: %d - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, mem_is_tainted(get_tag_address(src), count << 3),
                dst, count, mem_is_tainted(dst, count << 3));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * instrumentation helper; returns the flag that
 * takes as argument -- seems lame, but it is
 * necessary for aiding conditional analysis to
 * be inlined. Typically used with INS_InsertIfCall()
 * in order to return true (i.e., allow the execution
 * of the function that has been instrumented with
 * INS_InsertThenCall()) only once
 *
 * first_iteration:	flag; indicates whether the rep-prefixed instruction is
 * 			executed for the first time or not
 */
 ADDRINT PIN_FAST_ANALYSIS_CALL
rep_predicate(BOOL first_iteration, UINT32 opcode)
{
//    printf("REP prefixed ins %s\n", OPCODE_StringShort(opcode).c_str());
    /* return the flag; typically this is true only once */
	return first_iteration; 
}

/*
 * tag propagation (analysis function)
 *
 * restore the tag values for all the
 * 16-bit general purpose registers from
 * the memory
 *
 * NOTE: special case for POPA instruction 
 *
 * @thread_ctx:	the thread context
 * @src:	the source memory address	
 */
 void PIN_FAST_ANALYSIS_CALL
m2r_restore_opw(thread_ctx_t *thread_ctx, ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(mem_is_tainted(src, 16) ||
            *(((uint16_t *)&thread_ctx->vcpu.gpr[0])) ||
            *(((uint16_t *)&thread_ctx->vcpu.gpr[1])) ||
            *(((uint16_t *)&thread_ctx->vcpu.gpr[2])) ||
            *(((uint16_t *)&thread_ctx->vcpu.gpr[4])) ||
            *(((uint16_t *)&thread_ctx->vcpu.gpr[5])) ||
            *(((uint16_t *)&thread_ctx->vcpu.gpr[6])) ||
            *(((uint16_t *)&thread_ctx->vcpu.gpr[7])))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint 0x%x %u %u %u %u %u %u\n \
                dst regs: %u %u %u %u %u %u %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint16_t *)(get_tag_address(src))),
                *((uint16_t *)(src + get_tag_address(src + 2))),
                *((uint16_t *)(src + get_tag_address(src + 4))),
                *((uint16_t *)(src + get_tag_address(src + 8))),
                *((uint16_t *)(src + get_tag_address(src + 10))),
                *((uint16_t *)(src + get_tag_address(src + 12))),
                *((uint16_t *)(src + get_tag_address(src + 14))),
                *(((uint16_t *)&thread_ctx->vcpu.gpr[0])),
                *(((uint16_t *)&thread_ctx->vcpu.gpr[1])),
                *(((uint16_t *)&thread_ctx->vcpu.gpr[2])),
                *(((uint16_t *)&thread_ctx->vcpu.gpr[4])),
                *(((uint16_t *)&thread_ctx->vcpu.gpr[5])),
                *(((uint16_t *)&thread_ctx->vcpu.gpr[6])),
                *(((uint16_t *)&thread_ctx->vcpu.gpr[7])));
#endif

	/* tagmap address */
	ADDRINT dst = *(ADDRINT *)get_tag_address(src);

	/* restore DI */
	*((uint16_t *)&thread_ctx->vcpu.gpr[0]) = *(uint16_t *)dst;
	
	/* restore SI */
	*((uint16_t *)&thread_ctx->vcpu.gpr[1]) = *(uint16_t *)(dst + 2);
	
	/* restore BP */
	*((uint16_t *)&thread_ctx->vcpu.gpr[2]) = *(uint16_t *)(dst + 4);
	
	/* SP is ignored */
	
	/* restore BX */
	*((uint16_t *)&thread_ctx->vcpu.gpr[4]) = *(uint16_t *)(dst + 8);
	
	/* restore DX */
	*((uint16_t *)&thread_ctx->vcpu.gpr[5]) = *(uint16_t *)(dst + 10);
	
	/* restore CX */
	*((uint16_t *)&thread_ctx->vcpu.gpr[6]) = *(uint16_t *)(dst + 12);
	
	/* restore AX */
	*((uint16_t *)&thread_ctx->vcpu.gpr[7]) = *(uint16_t *)(dst + 14);
#ifdef PROPAGAION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src: %lx - taint 0x%x %u %u %u %u %u %u\n \
                dst regs: %u %u %u %u %u %u %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((uint16_t *)(get_tag_address(src))),
                *((uint16_t *)(src + get_tag_address(src + 2))),
                *((uint16_t *)(src + get_tag_address(src + 4))),
                *((uint16_t *)(src + get_tag_address(src + 8))),
                *((uint16_t *)(src + get_tag_address(src + 10))),
                *((uint16_t *)(src + get_tag_address(src + 12))),
                *((uint16_t *)(src + get_tag_address(src + 14))),
                *(((uint16_t *)&thread_ctx->vcpu.gpr[0])),
                *(((uint16_t *)&thread_ctx->vcpu.gpr[1])),
                *(((uint16_t *)&thread_ctx->vcpu.gpr[2])),
                *(((uint16_t *)&thread_ctx->vcpu.gpr[4])),
                *(((uint16_t *)&thread_ctx->vcpu.gpr[5])),
                *(((uint16_t *)&thread_ctx->vcpu.gpr[6])),
                *(((uint16_t *)&thread_ctx->vcpu.gpr[7])));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * restore the tag values for all the
 * 32-bit general purpose registers from
 * the memory
 *
 * NOTE: special case for POPAD instruction 
 *
 * @thread_ctx:	the thread context
 * @src:	the source memory address	
 */
 void PIN_FAST_ANALYSIS_CALL
m2r_restore_opl(thread_ctx_t *thread_ctx, ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGAION_DEBUG
    int tainted = 0;
    if(mem_is_tainted(src, 32) || 
            thread_ctx->vcpu.gpr[0] ||
            thread_ctx->vcpu.gpr[1] ||
            thread_ctx->vcpu.gpr[2] ||
            thread_ctx->vcpu.gpr[4] ||
            thread_ctx->vcpu.gpr[5] ||
            thread_ctx->vcpu.gpr[6] ||
            thread_ctx->vcpu.gpr[7])
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint 0x%x %u %u %u %u %u %u\n \
                dst regs: %lu %lu %lu %lu %lu %lu %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((UINT32 *)(get_tag_address(src))),
                *((UINT32 *)(src + get_tag_address(src + 4))),
                *((UINT32 *)(src + get_tag_address(src + 8))),
                *((UINT32 *)(src + get_tag_address(src + 16))),
                *((UINT32 *)(src + get_tag_address(src + 20))),
                *((UINT32 *)(src + get_tag_address(src + 24))),
                *((UINT32 *)(src + get_tag_address(src + 28))),
                thread_ctx->vcpu.gpr[0],
                thread_ctx->vcpu.gpr[1],
                thread_ctx->vcpu.gpr[2],
                thread_ctx->vcpu.gpr[4],
                thread_ctx->vcpu.gpr[5],
                thread_ctx->vcpu.gpr[6],
                thread_ctx->vcpu.gpr[7]);
#endif


	/* restore RDI */
	m2r_mov_32(thread_ctx, RDI, src);

	/* restore RSI */
	m2r_mov_32(thread_ctx, RSI, src + 4);
	
	/* restore RBP */
	m2r_mov_32(thread_ctx, RBP, src + 8);

	/* RSP is ignored */
	
	/* restore RBX */
	m2r_mov_32(thread_ctx, RBX, src + 16);
	
	/* restore RDX */
	m2r_mov_32(thread_ctx, RDX, src + 20);
	
	/* restore RCX */
	m2r_mov_32(thread_ctx, RCX, src + 24);
	
	/* restore RAX */
	m2r_mov_32(thread_ctx, RAX, src + 28);
#ifdef PROPAGAION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src: %lx - taint 0x%x %u %u %u %u %u %u\n \
                dst regs: %lu %lu %lu %lu %lu %lu %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((UINT32 *)(get_tag_address(src))),
                *((UINT32 *)(src + get_tag_address(src + 4))),
                *((UINT32 *)(src + get_tag_address(src + 8))),
                *((UINT32 *)(src + get_tag_address(src + 16))),
                *((UINT32 *)(src + get_tag_address(src + 20))),
                *((UINT32 *)(src + get_tag_address(src + 24))),
                *((UINT32 *)(src + get_tag_address(src + 28))),
                thread_ctx->vcpu.gpr[0],
                thread_ctx->vcpu.gpr[1],
                thread_ctx->vcpu.gpr[2],
                thread_ctx->vcpu.gpr[4],
                thread_ctx->vcpu.gpr[5],
                thread_ctx->vcpu.gpr[6],
                thread_ctx->vcpu.gpr[7]);
#endif
}

/*
 * tag propagation (analysis function)
 *
 * save the tag values for all the 16-bit
 * general purpose registers into the memory
 *
 * NOTE: special case for PUSHA instruction
 *
 * @thread_ctx:	the thread context
 * @dst:	the destination memory address
 */
 void PIN_FAST_ANALYSIS_CALL
r2m_save_opw(thread_ctx_t *thread_ctx, ADDRINT dst, UINT32 opcode)
{
	UINT64 dst_val = *(ADDRINT *)get_tag_address(dst);
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((uint16_t *)&thread_ctx->vcpu.gpr[0]))||
            *(((uint16_t *)&thread_ctx->vcpu.gpr[1]))||
            *(((uint16_t *)&thread_ctx->vcpu.gpr[2]))||
            *(((uint16_t *)&thread_ctx->vcpu.gpr[3]))||
            *(((uint16_t *)&thread_ctx->vcpu.gpr[4]))||
            *(((uint16_t *)&thread_ctx->vcpu.gpr[5]))||
            *(((uint16_t *)&thread_ctx->vcpu.gpr[6]))||
            *(((uint16_t *)&thread_ctx->vcpu.gpr[7])) ||
            mem_is_tainted(dst, 16))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg taints: %u %u %u %u %u %u %u %u\n \
                dst: %lx taints: %u %u %u %u %u %u %u\n",
                OPCODE_StringShort(opcode).c_str(),
                *(((uint16_t *)&thread_ctx->vcpu.gpr[0])),
                *(((uint16_t *)&thread_ctx->vcpu.gpr[1])),
                *(((uint16_t *)&thread_ctx->vcpu.gpr[2])),
                *(((uint16_t *)&thread_ctx->vcpu.gpr[3])),
                *(((uint16_t *)&thread_ctx->vcpu.gpr[4])),
                *(((uint16_t *)&thread_ctx->vcpu.gpr[5])),
                *(((uint16_t *)&thread_ctx->vcpu.gpr[6])),
                *(((uint16_t *)&thread_ctx->vcpu.gpr[7])),
                *(uint16_t *)(dst_val),
                *(uint16_t *)(dst_val + 2),
                *(uint16_t *)(dst_val + 4),
                *(uint16_t *)(dst_val + 6),
                *(uint16_t *)(dst_val + 8),
                *(uint16_t *)(dst_val + 10),
                *(uint16_t *)(dst_val + 12),
                *(uint16_t *)(dst_val + 14));
#endif
	/* tagmap address */

	/* save DI */
	*(uint16_t *)dst_val =  *((uint16_t *)&thread_ctx->vcpu.gpr[0]);

	/* save SI */
	*(uint16_t *)(dst_val + 2) = *((uint16_t *)&thread_ctx->vcpu.gpr[1]);

	/* save BP */
	*(uint16_t *)(dst_val + 4) = *((uint16_t *)&thread_ctx->vcpu.gpr[2]);

	/* save SP */
	*(uint16_t *)(dst_val + 6) = *((uint16_t *)&thread_ctx->vcpu.gpr[3]);

	/* save BX */
	*(uint16_t *)(dst_val + 8) = *((uint16_t *)&thread_ctx->vcpu.gpr[4]);

	/* save DX */
	*(uint16_t *)(dst_val + 10) = *((uint16_t *)&thread_ctx->vcpu.gpr[5]);

	/* save CX */
	*(uint16_t *)(dst_val + 12) = *((uint16_t *)&thread_ctx->vcpu.gpr[6]);

	/* save AX */
	*(uint16_t *)(dst_val + 14) = *((uint16_t *)&thread_ctx->vcpu.gpr[7]);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg taints: %u %u %u %u %u %u %u %u\n \
                dst: %lx taints: %u %u %u %u %u %u %u\n",
                OPCODE_StringShort(opcode).c_str(),
                *(((uint16_t *)&thread_ctx->vcpu.gpr[0])),
                *(((uint16_t *)&thread_ctx->vcpu.gpr[1])),
                *(((uint16_t *)&thread_ctx->vcpu.gpr[2])),
                *(((uint16_t *)&thread_ctx->vcpu.gpr[3])),
                *(((uint16_t *)&thread_ctx->vcpu.gpr[4])),
                *(((uint16_t *)&thread_ctx->vcpu.gpr[5])),
                *(((uint16_t *)&thread_ctx->vcpu.gpr[6])),
                *(((uint16_t *)&thread_ctx->vcpu.gpr[7])),
                *(uint16_t *)(dst_val),
                *(uint16_t *)(dst_val + 2),
                *(uint16_t *)(dst_val + 4),
                *(uint16_t *)(dst_val + 6),
                *(uint16_t *)(dst_val + 8),
                *(uint16_t *)(dst_val + 10),
                *(uint16_t *)(dst_val + 12),
                *(uint16_t *)(dst_val + 14));
#endif
}

/*
 * tag propagation (analysis function)
 *
 * save the tag values for all the 32-bit
 * general purpose registers into the memory
 *
 * NOTE: special case for PUSHAD instruction 
 *
 * @thread_ctx:	the thread context
 * @dst:	the destination memory address
 */
 void PIN_FAST_ANALYSIS_CALL
r2m_save_opl(thread_ctx_t *thread_ctx, ADDRINT dst, UINT32 opcode)
{
	/* tagmap address */
	ADDRINT dst_val = *(ADDRINT *)get_tag_address(dst);
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.gpr[0] ||
            thread_ctx->vcpu.gpr[1] ||
            thread_ctx->vcpu.gpr[2] ||
            thread_ctx->vcpu.gpr[3] ||
            thread_ctx->vcpu.gpr[4] ||
            thread_ctx->vcpu.gpr[5] ||
            thread_ctx->vcpu.gpr[6] ||
            thread_ctx->vcpu.gpr[7] ||
            mem_is_tainted(dst, 32))
        tainted = 1;
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src reg taints: %lu %lu %lu %lu %lu %lu %lu %lu\n \
            dst: %lx taints: %u %u %u %u %u %u %u\n",
                OPCODE_StringShort(opcode).c_str(),
                *(((UINT32 *)&thread_ctx->vcpu.gpr[0])),
                *(((UINT32 *)&thread_ctx->vcpu.gpr[1])),
                *(((UINT32 *)&thread_ctx->vcpu.gpr[2])),
                *(((UINT32 *)&thread_ctx->vcpu.gpr[3])),
                *(((UINT32 *)&thread_ctx->vcpu.gpr[4])),
                *(((UINT32 *)&thread_ctx->vcpu.gpr[5])),
                *(((UINT32 *)&thread_ctx->vcpu.gpr[6])),
                *(((UINT32 *)&thread_ctx->vcpu.gpr[7])),
                *(UINT32 *)(dst_val),
                *(UINT32 *)(dst_val + 4),
                *(UINT32 *)(dst_val + 8),
                *(UINT32 *)(dst_val + 12),
                *(UINT32 *)(dst_val + 16),
                *(UINT32 *)(dst_val + 20),
                *(UINT32 *)(dst_val + 24),
                *(UINT32 *)(dst_val + 28));
#endif

	/* save RDI */
	*(UINT32 *)dst_val = *((UINT32 *)&thread_ctx->vcpu.gpr[RDI]);

	/* save RSI */
	*(UINT32 *)(dst_val + 4) = *((UINT32 *)&thread_ctx->vcpu.gpr[RSI]);

	/* save RBP */
	*(UINT32 *)(dst_val + 8) = *((UINT32 *)&thread_ctx->vcpu.gpr[RBP]);

	/* save RSP */
	*(UINT32 *)(dst_val + 12) = *((UINT32 *)&thread_ctx->vcpu.gpr[RSP]);

	/* save RBX */
	*(UINT32 *)(dst_val + 16) = *((UINT32 *)&thread_ctx->vcpu.gpr[RBX]);

	/* save RDX */
	*(UINT32 *)(dst_val + 20) = *((UINT32 *)&thread_ctx->vcpu.gpr[RDX]);

	/* save RCX */
	*(UINT32 *)(dst_val + 24) = *((UINT32 *)&thread_ctx->vcpu.gpr[RCX]);

	/* save RAX */
	*(UINT32 *)(dst_val + 28) = *((UINT32 *)&thread_ctx->vcpu.gpr[RAX]);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src reg taints: %u %u %u %u %u %u %u %u\n \
                dst: %lx taints: %u %u %u %u %u %u %u\n",
                OPCODE_StringShort(opcode).c_str(),
                *(((UINT32 *)&thread_ctx->vcpu.gpr[0])),
                *(((UINT32 *)&thread_ctx->vcpu.gpr[1])),
                *(((UINT32 *)&thread_ctx->vcpu.gpr[2])),
                *(((UINT32 *)&thread_ctx->vcpu.gpr[3])),
                *(((UINT32 *)&thread_ctx->vcpu.gpr[4])),
                *(((UINT32 *)&thread_ctx->vcpu.gpr[5])),
                *(((UINT32 *)&thread_ctx->vcpu.gpr[6])),
                *(((UINT32 *)&thread_ctx->vcpu.gpr[7])),
                *(UINT32 *)(dst_val),
                *(UINT32 *)(dst_val + 4),
                *(UINT32 *)(dst_val + 8),
                *(UINT32 *)(dst_val + 12),
                *(UINT32 *)(dst_val + 16),
                *(UINT32 *)(dst_val + 20),
                *(UINT32 *)(dst_val + 24),
                *(UINT32 *)(dst_val + 28));
#endif
}


//New analysis functions
/*
 * Propagates the union of the taint from two 32/64-bit registers 
 * to a third 32/64-bit register.
 * dst = src1 | src2
 */
 void rr2r_binary_opl(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src1, UINT32 src2, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.gpr[src1] || thread_ctx->vcpu.gpr[src2]
            || thread_ctx->vcpu.gpr[dst])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src1 reg: %u - taint %lu src2 reg: %u taint %lu \
                dst reg: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src1, thread_ctx->vcpu.gpr[src1],
                src2, thread_ctx->vcpu.gpr[src2],
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
	thread_ctx->vcpu.gpr[dst] = 
        thread_ctx->vcpu.gpr[src1] | thread_ctx->vcpu.gpr[src2];
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src1 reg: %u - taint %lu src2 reg: %u taint %lu \
                dst reg: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src1, thread_ctx->vcpu.gpr[src1],
                src2, thread_ctx->vcpu.gpr[src2],
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
}


/*
 * Propagates the union of the taint from a 64-bit register(src1) and memory 
 * location(src2) to a 64-bit register(dst), where taint propagates as follows:
 * dst = src1 | src2
 */
 void 
rm2r_binary_opqw(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src1, ADDRINT src2, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.gpr[src1] || *(ADDRINT *)get_tag_address(src2)
            || thread_ctx->vcpu.gpr[dst])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src1 reg: %u - taint %lu src2 reg: %u taint %lu \
                dst reg: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src1, thread_ctx->vcpu.gpr[src1],
                src2, *(ADDRINT *)get_tag_address(src2),
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
	thread_ctx->vcpu.gpr[dst] = 
        thread_ctx->vcpu.gpr[src1] | *(ADDRINT *)get_tag_address(src2);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src1 reg: %u - taint %lu src2 reg: %u taint %lu \
                dst reg: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src1, thread_ctx->vcpu.gpr[src1],
                src2, *(ADDRINT *)get_tag_address(src2),
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
}

/*
 * Propagates the union of the taint from a 32-bit register(src) and memory 
 * location(src2) to a 32-bit register(dst). Taint propagates as follows:
 * dst = src1 | src2
 */
 void 
rm2r_binary_opl(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src1, ADDRINT src2, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((UINT32 *)&thread_ctx->vcpu.gpr[src1]) || 
            *(UINT32 *)get_tag_address(src2) ||
            *((UINT32 *)&thread_ctx->vcpu.gpr[dst]))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src1 reg: %u - taint %lu src2 reg: %u taint %lu \
                dst reg: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src1, *((UINT32 *)&thread_ctx->vcpu.gpr[src1]),
                src2, *(UINT32 *)get_tag_address(src2),
                dst, *((UINT32 *)&thread_ctx->vcpu.gpr[dst]));
#endif
	thread_ctx->vcpu.gpr[dst] = 
        thread_ctx->vcpu.gpr[src1] | *(ADDRINT *)get_tag_address(src2);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src1 reg: %u - taint %lu src2 reg: %u taint %lu \
                dst reg: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src1, *((UINT32 *)&thread_ctx->vcpu.gpr[src1]),
                src2, *(UINT32 *)get_tag_address(src2),
                dst, *((UINT32 *)&thread_ctx->vcpu.gpr[dst]));
#endif
}


// shift instructions /////////////////////////////////////////////////////////


/*
 * General shift operation taint propagation:
 * Shifts dst operand to left or right count bits. If the bitshift results in 
 * byte taint tags overlapping byte-boundaries, we must take the union of the 
 * two byte taint tags. If count is a register, take the union of the count 
 * taint with all bytes 
 *      if count % 8 == 0: // whole byte shift
 *          t[dst] = t[dst] <</>> (count/8)
 *      else // overlapping byte taint tags
 *          t[dst] = t[dst] <</>> (count/8) | t[dst] <</>> (count/8 + 1)
 *      for each byte in t[dst]:
 *          t[dst] |= t[count]
 */

/*
 * @ dst: 64-bit register
 * @ count: CL reg - number of bits to shift. Masked to  6 bits 
 * @ count_reg: 8 bit register containting count (for taint)
 */
VOID shiftl_r_cl_bits_2op64(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT64 count, UINT32 count_reg, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.gpr[dst] | *(UINT8 *)&thread_ctx->vcpu.gpr[count_reg])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
#endif
    UINT64 tmp_tag = thread_ctx->vcpu.gpr[dst];
    
    // shift dst taints based on count
    thread_ctx->vcpu.gpr[dst] = 
            tmp_tag << BYTE_ALIGN(count & SHIFT_MASK64);
    // If byte tags overlap, take the union of tag of the overlapping byte.
    // TODO: eliminate if?
    if(count % 8)
    thread_ctx->vcpu.gpr[dst] |= 
            tmp_tag << (BYTE_ALIGN(count & SHIFT_MASK64) + BYTE_BITS);
    
    // if count is tainted, take the union of count's taint with each byte
    UINT8 count_tag = *(UINT8 *)&thread_ctx->vcpu.gpr[count_reg];
    for(UINT8 i = 0; i < BIT2BYTE(QWORD_BITS); i++)
        *(((UINT8 *)&thread_ctx->vcpu.gpr[dst]) + i) |= count_tag;

#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst reg: %u - taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
}

/*
 * @ dst: 64-bit register
 * @ count: imm - number of bits to shift. Masked to  6 bits 
 */
VOID shiftl_r_imm_bits_2op64(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.gpr[dst])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
#endif
    UINT64 tmp_tag = thread_ctx->vcpu.gpr[dst];
    
    // shift dst taints based on count
    thread_ctx->vcpu.gpr[dst] = 
            tmp_tag << BYTE_ALIGN(count & SHIFT_MASK64);
    // If byte tags overlap, take the union of tag of the overlapping byte.
    // TODO: eliminate if?
    if(count % 8)
    thread_ctx->vcpu.gpr[dst] |= 
            tmp_tag << (BYTE_ALIGN(count & SHIFT_MASK64) + BYTE_BITS);

#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst reg: %u - taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
}


/*
 * @ dst: 32-bit register
 * @ count: cl reg - number of bits to shift. Masked to  6 bits 
 * @ count_reg: 8 bit register containting count (for taint)
 */
VOID shiftl_r_cl_bits_2op32(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT64 count, UINT32 count_reg, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.gpr[dst])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    
#endif
    UINT32 tmp_tag = *(UINT32 *)&thread_ctx->vcpu.gpr[dst];
    
    thread_ctx->vcpu.gpr[dst] = 
        tmp_tag << BYTE_ALIGN(count & SHIFT_MASK);
    // If byte tags overlap, take the union of tag of the overlapping byte
    if(count % 8)
        thread_ctx->vcpu.gpr[dst] |= 
            tmp_tag << (BYTE_ALIGN(count & SHIFT_MASK) + BYTE_BITS);
    
    // if count is tainted, take the union of count's taint with each byte
    UINT8 count_tag = *(UINT8 *)&thread_ctx->vcpu.gpr[count_reg];
    for(UINT8 i = 0; i < BIT2BYTE(DWORD_BITS); i++)
        *(((UINT8 *)&thread_ctx->vcpu.gpr[dst]) + i) |= count_tag;
    
    // Zero the upper 32 bits
    *(((UINT32 *)&thread_ctx->vcpu.gpr[dst]) + 1) = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst reg: %u - taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
}

/*
 * @ dst: 32-bit register
 * @ count: imm - number of bits to shift. Masked to  6 bits 
 */
VOID shiftl_r_imm_bits_2op32(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.gpr[dst])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    
#endif
    UINT32 tmp_tag = *(UINT32 *)&thread_ctx->vcpu.gpr[dst];
    
    thread_ctx->vcpu.gpr[dst] = 
        tmp_tag << BYTE_ALIGN(count & SHIFT_MASK);
    // If byte tags overlap, take the union of tag of the overlapping byte
    if(count % 8)
        thread_ctx->vcpu.gpr[dst] |= 
            tmp_tag << (BYTE_ALIGN(count & SHIFT_MASK) + BYTE_BITS);
    
    // Zero the upper 32 bits
    *(((UINT32 *)&thread_ctx->vcpu.gpr[dst]) + 1) = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst reg: %u - taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
}

/*
 * @ dst: 16-bit register
 * @ count: cl reg - number of bits to shift. Masked to  6 bits 
 * @ count_reg: 8 bit register containting count (for taint)
 */
VOID shiftl_r_cl_bits_2op16(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT64 count, UINT32 count_reg, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((UINT16 *)&thread_ctx->vcpu.gpr[dst]))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    
#endif
    UINT16 tmp_tag = *(UINT8 *)&thread_ctx->vcpu.gpr[dst];
    
    *(UINT16 *)&thread_ctx->vcpu.gpr[dst] = 
        tmp_tag << BYTE_ALIGN(count & SHIFT_MASK);
    // If byte tags overlap, take the union of tag of the overlapping byte
    if(count % 8)
        *(UINT16 *)&thread_ctx->vcpu.gpr[dst] |= 
            tmp_tag << (BYTE_ALIGN(count & SHIFT_MASK) + BYTE_BITS);
    
    // if count is tainted, take the union of count's taint with each byte
    UINT8 count_tag = *(UINT8 *)&thread_ctx->vcpu.gpr[count_reg];
    for(UINT8 i = 0; i < BIT2BYTE(WORD_BITS); i++)
        *(((UINT8 *)&thread_ctx->vcpu.gpr[dst]) + i)  |= count_tag;
    
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst reg: %u - taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *((UINT16 *)&thread_ctx->vcpu.gpr[dst]));
#endif
}

/*
 * @ dst: 16-bit register
 * @ count: imm - number of bits to shift. Masked to  6 bits 
 */
VOID shiftl_r_imm_bits_2op16(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((UINT16 *)&thread_ctx->vcpu.gpr[dst]))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    
#endif
    UINT16 tmp_tag = *(UINT8 *)&thread_ctx->vcpu.gpr[dst];
    
    *(UINT16 *)&thread_ctx->vcpu.gpr[dst] = 
        tmp_tag << BYTE_ALIGN(count & SHIFT_MASK);
    // If byte tags overlap, take the union of tag of the overlapping byte
    if(count % 8)
        *(UINT16 *)&thread_ctx->vcpu.gpr[dst] |= 
            tmp_tag << (BYTE_ALIGN(count & SHIFT_MASK) + BYTE_BITS);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst reg: %u - taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *((UINT16 *)&thread_ctx->vcpu.gpr[dst]));
#endif
}

/*
 * @ dst: 8-bit lower register
 * @ count: cl reg - number of bits to shift. Masked to  6 bits 
 * @ count_reg: 8 bit register containting count (for taint)
 */
VOID shiftl_r_cl_bits_2op8l(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT64 count, UINT32 count_reg, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((UINT8 *)&thread_ctx->vcpu.gpr[dst]))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    
#endif
    UINT8 tmp_tag = *(UINT8 *)&thread_ctx->vcpu.gpr[dst];
    
    *(UINT8 *)&thread_ctx->vcpu.gpr[dst] = 
        tmp_tag << BYTE_ALIGN(count & SHIFT_MASK);
    // If byte tags overlap, take the union of tag of the overlapping byte
    if(count % 8)
        *(UINT8 *)&thread_ctx->vcpu.gpr[dst] |= 
            tmp_tag << (BYTE_ALIGN(count & SHIFT_MASK) + BYTE_BITS);
    
    // if count is tainted, take the union of count's taint with each byte
    UINT8 count_tag = *(UINT8 *)&thread_ctx->vcpu.gpr[count_reg];
    thread_ctx->vcpu.gpr[dst] |= count_tag;
    
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst reg: %u - taint %x\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *((UINT8 *)&thread_ctx->vcpu.gpr[dst]));
#endif
}

/*
 * @ dst: 8-bit lower register
 * @ count: imm- number of bits to shift. Masked to  6 bits 
 */
VOID shiftl_r_imm_bits_2op8l(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((UINT8 *)&thread_ctx->vcpu.gpr[dst]))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    
#endif
    UINT8 tmp_tag = *(UINT8 *)&thread_ctx->vcpu.gpr[dst];
    
    *(UINT8 *)&thread_ctx->vcpu.gpr[dst] = 
        tmp_tag << BYTE_ALIGN(count & SHIFT_MASK);
    // If byte tags overlap, take the union of tag of the overlapping byte
    if(count % 8)
        *(UINT8 *)&thread_ctx->vcpu.gpr[dst] |= 
            tmp_tag << (BYTE_ALIGN(count & SHIFT_MASK) + BYTE_BITS);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst reg: %u - taint %x\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *((UINT8 *)&thread_ctx->vcpu.gpr[dst]));
#endif
}

/*
 * @ dst: 8-bit upper register
 * @ count: cl reg - number of bits to shift. Masked to  6 bits 
 * @ count_reg: 8 bit register containting count (for taint)
 */
VOID shiftl_r_cl_bits_2op8u(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT64 count, UINT32 count_reg, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((UINT8 *)&thread_ctx->vcpu.gpr[dst]) + 1))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
#endif
    UINT8 tmp_tag = *(((UINT8 *)&thread_ctx->vcpu.gpr[dst]) + 1);
    
    *(((UINT8 *)&thread_ctx->vcpu.gpr[dst]) + 1) = 
        tmp_tag << BYTE_ALIGN(count & SHIFT_MASK);
    // If byte tags overlap, take the union of tag of the overlapping byte
    if(count % 8)
        *(((UINT8 *)&thread_ctx->vcpu.gpr[dst]) + 1) |= 
            tmp_tag << (BYTE_ALIGN(count & SHIFT_MASK) + BYTE_BITS);
    
    // if count is tainted, take the union of count's taint with each byte
    UINT8 count_tag = *(UINT8 *)&thread_ctx->vcpu.gpr[count_reg];
    *(((UINT8 *)&thread_ctx->vcpu.gpr[dst]) + 1)  |= count_tag;
    
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst reg: %u - taint %x\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(((UINT8 *)&thread_ctx->vcpu.gpr[dst]) + 1));
#endif
}

/*
 * @ dst: 8-bit upper register
 * @ count: imm - number of bits to shift. Masked to  6 bits 
 */
VOID shiftl_r_imm_bits_2op8u(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((UINT8 *)&thread_ctx->vcpu.gpr[dst]) + 1))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
#endif
    UINT8 tmp_tag = *(((UINT8 *)&thread_ctx->vcpu.gpr[dst]) + 1);
    
    *(((UINT8 *)&thread_ctx->vcpu.gpr[dst]) + 1) = 
        tmp_tag << BYTE_ALIGN(count & SHIFT_MASK);
    // If byte tags overlap, take the union of tag of the overlapping byte
    if(count % 8)
        *(((UINT8 *)&thread_ctx->vcpu.gpr[dst]) + 1) |= 
            tmp_tag << (BYTE_ALIGN(count & SHIFT_MASK) + BYTE_BITS);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst reg: %u - taint %x\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(((UINT8 *)&thread_ctx->vcpu.gpr[dst]) + 1));
#endif
}

/*
 * @ dst: 64-bit memory operand
 * @ count: cl reg - number of bits to shift. Masked to  6 bits 
 * @ count_reg: 8 bit register containting count (for taint)
 */
VOID shiftl_m_cl_bits_2op64(thread_ctx_t *thread_ctx, ADDRINT dst, 
        UINT64 count, UINT32 count_reg, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(UINT64 *)get_tag_address(dst))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    
#endif
    UINT64 tmp_tag = *(UINT64 *)get_tag_address(dst);
    
    *(UINT64 *)get_tag_address(dst) = 
        tmp_tag << BYTE_ALIGN(count & SHIFT_MASK64);
    // If byte tags overlap, take the union of tag of the overlapping byte
    if(count % 8)
        *(UINT64 *)get_tag_address(dst) |= 
           tmp_tag << (BYTE_ALIGN(count & SHIFT_MASK64) + BYTE_BITS);
    
    // if count is tainted, take the union of count's taint with each byte
    UINT8 count_tag = *(UINT8 *)&thread_ctx->vcpu.gpr[count_reg];
    for(UINT8 i = 0; i < BIT2BYTE(QWORD_BITS); i++)
        *(((UINT8 *)get_tag_address(dst)) + i)  |= count_tag;
    
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst: %lx taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(UINT64 *)get_tag_address(dst));
#endif
}

/*
 * @ dst: 64-bit memory operand
 * @ count: imm - number of bits to shift. Masked to  6 bits 
 */
VOID shiftl_m_imm_bits_2op64(thread_ctx_t *thread_ctx, ADDRINT dst, 
        UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(UINT64 *)get_tag_address(dst))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    
#endif
    UINT64 tmp_tag = *(UINT64 *)get_tag_address(dst);
    
    *(UINT64 *)get_tag_address(dst) = 
        tmp_tag << BYTE_ALIGN(count & SHIFT_MASK64);
    // If byte tags overlap, take the union of tag of the overlapping byte
    if(count % 8)
        *(UINT64 *)get_tag_address(dst) |= 
           tmp_tag << (BYTE_ALIGN(count & SHIFT_MASK64) + BYTE_BITS);
    
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst: %lx taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(UINT64 *)get_tag_address(dst));
#endif
}

/*
 * @ dst: 32-bit memory operand
 * @ count: cl reg - number of bits to shift. Masked to  6 bits 
 * @ count_reg: 8 bit register containting count (for taint)
 */
VOID shiftl_m_cl_bits_2op32(thread_ctx_t *thread_ctx, ADDRINT dst, 
        UINT64 count, UINT32 count_reg, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(UINT32 *)get_tag_address(dst))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    
#endif
    UINT32 tmp_tag = *(UINT32 *)get_tag_address(dst);
    
    *(UINT32 *)get_tag_address(dst) = 
        tmp_tag << BYTE_ALIGN(count & SHIFT_MASK);
    // If byte tags overlap, take the union of tag of the overlapping byte
    if(count % 8)
        *(UINT32 *)get_tag_address(dst) |= 
            tmp_tag << (BYTE_ALIGN(count & SHIFT_MASK) + BYTE_BITS);
    
    // if count is tainted, take the union of count's taint with each byte
    UINT8 count_tag = *(UINT8 *)&thread_ctx->vcpu.gpr[count_reg];
    for(UINT8 i = 0; i < BIT2BYTE(DWORD_BITS); i++)
        *(((UINT8 *)get_tag_address(dst)) + i)  |= count_tag;
    // Zero the upper 32 bits
    *(((UINT32 *)get_tag_address(dst)) + 1) = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst: %lx taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(UINT32 *)get_tag_address(dst));
#endif
}

/*
 * @ dst: 32-bit memory operand
 * @ count: imm - number of bits to shift. Masked to  6 bits 
 */
VOID shiftl_m_imm_bits_2op32(thread_ctx_t *thread_ctx, ADDRINT dst, 
        UINT64 count, UINT32 count_reg, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(UINT32 *)get_tag_address(dst))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    
#endif
    UINT32 tmp_tag = *(UINT32 *)get_tag_address(dst);
    
    *(UINT32 *)get_tag_address(dst) = 
        tmp_tag << BYTE_ALIGN(count & SHIFT_MASK);
    // If byte tags overlap, take the union of tag of the overlapping byte
    if(count % 8)
        *(UINT32 *)get_tag_address(dst) |= 
            tmp_tag << (BYTE_ALIGN(count & SHIFT_MASK) + BYTE_BITS);
    
    // Zero the upper 32 bits
    *(((UINT32 *)get_tag_address(dst)) + 1) = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst: %lx taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(UINT32 *)get_tag_address(dst));
#endif
}

/*
 * @ dst: 16-bit memory operand
 * @ count: cl reg - number of bits to shift. Masked to  6 bits 
 * @ count_reg: 8 bit register containting count (for taint)
 */
VOID shiftl_m_cl_bits_2op16(thread_ctx_t *thread_ctx, ADDRINT dst, 
        UINT64 count, UINT32 count_reg, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(UINT16 *)get_tag_address(dst))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    
#endif
    UINT16 tmp_tag = *(UINT16 *)get_tag_address(dst);
    
    *(UINT16 *)get_tag_address(dst) = 
        tmp_tag << BYTE_ALIGN(count & SHIFT_MASK);
    // If byte tags overlap, take the union of tag of the overlapping byte
    if(count % 8)
        *(UINT16 *)get_tag_address(dst) |= 
            tmp_tag << (BYTE_ALIGN(count & SHIFT_MASK) + BYTE_BITS);
    
    // if count is tainted, take the union of count's taint with each byte
    UINT8 count_tag = *(UINT8 *)&thread_ctx->vcpu.gpr[count_reg];
    for(UINT8 i = 0; i < BIT2BYTE(WORD_BITS); i++)
        *(((UINT8 *)get_tag_address(dst)) + i)  |= count_tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst: %lx taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(UINT16 *)get_tag_address(dst));
#endif
}

/*
 * @ dst: 16-bit memory operand
 * @ count: imm - number of bits to shift. Masked to  6 bits 
 */
VOID shiftl_m_imm_bits_2op16(thread_ctx_t *thread_ctx, ADDRINT dst, 
        UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(UINT16 *)get_tag_address(dst))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    
#endif
    UINT16 tmp_tag = *(UINT16 *)get_tag_address(dst);
    
    *(UINT16 *)get_tag_address(dst) = 
        tmp_tag << BYTE_ALIGN(count & SHIFT_MASK);
    // If byte tags overlap, take the union of tag of the overlapping byte
    if(count % 8)
        *(UINT16 *)get_tag_address(dst) |= 
            tmp_tag << (BYTE_ALIGN(count & SHIFT_MASK) + BYTE_BITS);
    
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst: %lx taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(UINT16 *)get_tag_address(dst));
#endif
}

/*
 * @ dst: 8-bit memory operand
 * @ count: cl reg - number of bits to shift. Masked to  6 bits 
 * @ count_reg: 8 bit register containting count (for taint)
 */
VOID shiftl_m_cl_bits_2op8(thread_ctx_t *thread_ctx, ADDRINT dst, 
        UINT64 count, UINT32 count_reg, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(UINT8 *)get_tag_address(dst))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    
#endif
    UINT8 tmp_tag = *(UINT8 *)get_tag_address(dst);
    
    *(UINT8 *)get_tag_address(dst) = 
        tmp_tag << BYTE_ALIGN(count & SHIFT_MASK);
    // If byte tags overlap, take the union of tag of the overlapping byte
    if(count % 8)
        *(UINT8 *)get_tag_address(dst) |= 
            tmp_tag << (BYTE_ALIGN(count & SHIFT_MASK) + BYTE_BITS);
    
    // if count is tainted, take the union of count's taint with each byte
    UINT8 count_tag = *(UINT8 *)&thread_ctx->vcpu.gpr[count_reg];
    *((UINT8 *)get_tag_address(dst))  |= count_tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst: %lx taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(UINT64 *)get_tag_address(dst));
#endif
}

/*
 * @ dst: 8-bit memory operand
 * @ count: imm - number of bits to shift. Masked to  6 bits 
 */
VOID shiftl_m_imm_bits_2op8(thread_ctx_t *thread_ctx, ADDRINT dst, 
        UINT64 count, UINT32 count_reg, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(UINT8 *)get_tag_address(dst))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    
#endif
    UINT8 tmp_tag = *(UINT8 *)get_tag_address(dst);
    
    *(UINT8 *)get_tag_address(dst) = 
        tmp_tag << BYTE_ALIGN(count & SHIFT_MASK);
    // If byte tags overlap, take the union of tag of the overlapping byte
    if(count % 8)
        *(UINT8 *)get_tag_address(dst) |= 
            tmp_tag << (BYTE_ALIGN(count & SHIFT_MASK) + BYTE_BITS);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst: %lx taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(UINT64 *)get_tag_address(dst));
#endif
}

/*
 * @ dst: 64-bit register
 * @ count: CL reg - number of bits to shift. Masked to  6 bits 
 * @ count_reg: 8 bit register containting count (for taint)
 */
VOID shiftr_r_cl_bits_2op64(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT64 count, UINT32 count_reg, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.gpr[dst] | *(UINT8 *)&thread_ctx->vcpu.gpr[count_reg])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
#endif
    UINT64 tmp_tag = thread_ctx->vcpu.gpr[dst];
    
    // shift dst taints based on count
    thread_ctx->vcpu.gpr[dst] = 
            tmp_tag >> BYTE_ALIGN(count & SHIFT_MASK64);
    // If byte tags overlap, take the union of tag of the overlapping byte.
    // TODO: eliminate if?
    if(count % 8)
    thread_ctx->vcpu.gpr[dst] |= 
            tmp_tag >> (BYTE_ALIGN(count & SHIFT_MASK64) + BYTE_BITS);
    
    // if count is tainted, take the union of count's taint with each byte
    UINT8 count_tag = *(UINT8 *)&thread_ctx->vcpu.gpr[count_reg];
    for(UINT8 i = 0; i < BIT2BYTE(QWORD_BITS); i++)
        *(((UINT8 *)&thread_ctx->vcpu.gpr[dst]) + i) |= count_tag;

#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst reg: %u - taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
}

/*
 * @ dst: 64-bit register
 * @ count: imm - number of bits to shift. Masked to  6 bits 
 */
VOID shiftr_r_imm_bits_2op64(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.gpr[dst])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
#endif
    UINT64 tmp_tag = thread_ctx->vcpu.gpr[dst];
    
    // shift dst taints based on count
    thread_ctx->vcpu.gpr[dst] = 
            tmp_tag >> BYTE_ALIGN(count & SHIFT_MASK64);
    // If byte tags overlap, take the union of tag of the overlapping byte.
    // TODO: eliminate if?
    if(count % 8)
    thread_ctx->vcpu.gpr[dst] |= 
            tmp_tag >> (BYTE_ALIGN(count & SHIFT_MASK64) + BYTE_BITS);

#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst reg: %u - taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
}


/*
 * @ dst: 32-bit register
 * @ count: cl reg - number of bits to shift. Masked to  6 bits 
 * @ count_reg: 8 bit register containting count (for taint)
 */
VOID shiftr_r_cl_bits_2op32(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT64 count, UINT32 count_reg, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.gpr[dst])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    
#endif
    UINT32 tmp_tag = *(UINT32 *)&thread_ctx->vcpu.gpr[dst];
    
    thread_ctx->vcpu.gpr[dst] = 
        tmp_tag >> BYTE_ALIGN(count & SHIFT_MASK);
    // If byte tags overlap, take the union of tag of the overlapping byte
    if(count % 8)
        thread_ctx->vcpu.gpr[dst] |= 
            tmp_tag >> (BYTE_ALIGN(count & SHIFT_MASK) + BYTE_BITS);
    
    // if count is tainted, take the union of count's taint with each byte
    UINT8 count_tag = *(UINT8 *)&thread_ctx->vcpu.gpr[count_reg];
    for(UINT8 i = 0; i < BIT2BYTE(DWORD_BITS); i++)
        *(((UINT8 *)&thread_ctx->vcpu.gpr[dst]) + i) |= count_tag;
    
    // Zero the upper 32 bits
    *(((UINT32 *)&thread_ctx->vcpu.gpr[dst]) + 1) = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst reg: %u - taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
}

/*
 * @ dst: 32-bit register
 * @ count: imm - number of bits to shift. Masked to  6 bits 
 */
VOID shiftr_r_imm_bits_2op32(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.gpr[dst])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    
#endif
    UINT32 tmp_tag = *(UINT32 *)&thread_ctx->vcpu.gpr[dst];
    
    thread_ctx->vcpu.gpr[dst] = 
        tmp_tag >> BYTE_ALIGN(count & SHIFT_MASK);
    // If byte tags overlap, take the union of tag of the overlapping byte
    if(count % 8)
        thread_ctx->vcpu.gpr[dst] |= 
            tmp_tag >> (BYTE_ALIGN(count & SHIFT_MASK) + BYTE_BITS);
    
    // Zero the upper 32 bits
    *(((UINT32 *)&thread_ctx->vcpu.gpr[dst]) + 1) = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst reg: %u - taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
}

/*
 * @ dst: 16-bit register
 * @ count: cl reg - number of bits to shift. Masked to  6 bits 
 * @ count_reg: 8 bit register containting count (for taint)
 */
VOID shiftr_r_cl_bits_2op16(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT64 count, UINT32 count_reg, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((UINT16 *)&thread_ctx->vcpu.gpr[dst]))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    
#endif
    UINT16 tmp_tag = *(UINT8 *)&thread_ctx->vcpu.gpr[dst];
    
    *(UINT16 *)&thread_ctx->vcpu.gpr[dst] = 
        tmp_tag >> BYTE_ALIGN(count & SHIFT_MASK);
    // If byte tags overlap, take the union of tag of the overlapping byte
    if(count % 8)
        *(UINT16 *)&thread_ctx->vcpu.gpr[dst] |= 
            tmp_tag >> (BYTE_ALIGN(count & SHIFT_MASK) + BYTE_BITS);
    
    // if count is tainted, take the union of count's taint with each byte
    UINT8 count_tag = *(UINT8 *)&thread_ctx->vcpu.gpr[count_reg];
    for(UINT8 i = 0; i < BIT2BYTE(WORD_BITS); i++)
        *(((UINT8 *)&thread_ctx->vcpu.gpr[dst]) + i)  |= count_tag;
    
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst reg: %u - taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *((UINT16 *)&thread_ctx->vcpu.gpr[dst]));
#endif
}

/*
 * @ dst: 16-bit register
 * @ count: imm - number of bits to shift. Masked to  6 bits 
 */
VOID shiftr_r_imm_bits_2op16(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((UINT16 *)&thread_ctx->vcpu.gpr[dst]))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    
#endif
    UINT16 tmp_tag = *(UINT8 *)&thread_ctx->vcpu.gpr[dst];
    
    *(UINT16 *)&thread_ctx->vcpu.gpr[dst] = 
        tmp_tag >> BYTE_ALIGN(count & SHIFT_MASK);
    // If byte tags overlap, take the union of tag of the overlapping byte
    if(count % 8)
        *(UINT16 *)&thread_ctx->vcpu.gpr[dst] |= 
            tmp_tag >> (BYTE_ALIGN(count & SHIFT_MASK) + BYTE_BITS);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst reg: %u - taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *((UINT16 *)&thread_ctx->vcpu.gpr[dst]));
#endif
}

/*
 * @ dst: 8-bit lower register
 * @ count: cl reg - number of bits to shift. Masked to  6 bits 
 * @ count_reg: 8 bit register containting count (for taint)
 */
VOID shiftr_r_cl_bits_2op8l(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT64 count, UINT32 count_reg, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((UINT8 *)&thread_ctx->vcpu.gpr[dst]))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    
#endif
    UINT8 tmp_tag = *(UINT8 *)&thread_ctx->vcpu.gpr[dst];
    
    *(UINT8 *)&thread_ctx->vcpu.gpr[dst] = 
        tmp_tag >> BYTE_ALIGN(count & SHIFT_MASK);
    // If byte tags overlap, take the union of tag of the overlapping byte
    if(count % 8)
        *(UINT8 *)&thread_ctx->vcpu.gpr[dst] |= 
            tmp_tag >> (BYTE_ALIGN(count & SHIFT_MASK) + BYTE_BITS);
    
    // if count is tainted, take the union of count's taint with each byte
    UINT8 count_tag = *(UINT8 *)&thread_ctx->vcpu.gpr[count_reg];
    thread_ctx->vcpu.gpr[dst] |= count_tag;
    
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst reg: %u - taint %x\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *((UINT8 *)&thread_ctx->vcpu.gpr[dst]));
#endif
}

/*
 * @ dst: 8-bit lower register
 * @ count: imm- number of bits to shift. Masked to  6 bits 
 */
VOID shiftr_r_imm_bits_2op8l(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((UINT8 *)&thread_ctx->vcpu.gpr[dst]))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    
#endif
    UINT8 tmp_tag = *(UINT8 *)&thread_ctx->vcpu.gpr[dst];
    
    *(UINT8 *)&thread_ctx->vcpu.gpr[dst] = 
        tmp_tag >> BYTE_ALIGN(count & SHIFT_MASK);
    // If byte tags overlap, take the union of tag of the overlapping byte
    if(count % 8)
        *(UINT8 *)&thread_ctx->vcpu.gpr[dst] |= 
            tmp_tag >> (BYTE_ALIGN(count & SHIFT_MASK) + BYTE_BITS);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst reg: %u - taint %x\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *((UINT8 *)&thread_ctx->vcpu.gpr[dst]));
#endif
}

/*
 * @ dst: 8-bit upper register
 * @ count: cl reg - number of bits to shift. Masked to  6 bits 
 * @ count_reg: 8 bit register containting count (for taint)
 */
VOID shiftr_r_cl_bits_2op8u(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT64 count, UINT32 count_reg, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((UINT8 *)&thread_ctx->vcpu.gpr[dst]) + 1))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
#endif
    UINT8 tmp_tag = *(((UINT8 *)&thread_ctx->vcpu.gpr[dst]) + 1);
    
    *(((UINT8 *)&thread_ctx->vcpu.gpr[dst]) + 1) = 
        tmp_tag >> BYTE_ALIGN(count & SHIFT_MASK);
    // If byte tags overlap, take the union of tag of the overlapping byte
    if(count % 8)
        *(((UINT8 *)&thread_ctx->vcpu.gpr[dst]) + 1) |= 
            tmp_tag >> (BYTE_ALIGN(count & SHIFT_MASK) + BYTE_BITS);
    
    // if count is tainted, take the union of count's taint with each byte
    UINT8 count_tag = *(UINT8 *)&thread_ctx->vcpu.gpr[count_reg];
    *(((UINT8 *)&thread_ctx->vcpu.gpr[dst]) + 1)  |= count_tag;
    
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst reg: %u - taint %x\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(((UINT8 *)&thread_ctx->vcpu.gpr[dst]) + 1));
#endif
}

/*
 * @ dst: 8-bit upper register
 * @ count: imm - number of bits to shift. Masked to  6 bits 
 */
VOID shiftr_r_imm_bits_2op8u(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((UINT8 *)&thread_ctx->vcpu.gpr[dst]) + 1))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
#endif
    UINT8 tmp_tag = *(((UINT8 *)&thread_ctx->vcpu.gpr[dst]) + 1);
    
    *(((UINT8 *)&thread_ctx->vcpu.gpr[dst]) + 1) = 
        tmp_tag >> BYTE_ALIGN(count & SHIFT_MASK);
    // If byte tags overlap, take the union of tag of the overlapping byte
    if(count % 8)
        *(((UINT8 *)&thread_ctx->vcpu.gpr[dst]) + 1) |= 
            tmp_tag >> (BYTE_ALIGN(count & SHIFT_MASK) + BYTE_BITS);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst reg: %u - taint %x\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(((UINT8 *)&thread_ctx->vcpu.gpr[dst]) + 1));
#endif
}

/*
 * @ dst: 64-bit memory operand
 * @ count: cl reg - number of bits to shift. Masked to  6 bits 
 * @ count_reg: 8 bit register containting count (for taint)
 */
VOID shiftr_m_cl_bits_2op64(thread_ctx_t *thread_ctx, ADDRINT dst, 
        UINT64 count, UINT32 count_reg, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(UINT64 *)get_tag_address(dst))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    
#endif
    UINT64 tmp_tag = *(UINT64 *)get_tag_address(dst);
    
    *(UINT64 *)get_tag_address(dst) = 
        tmp_tag >> BYTE_ALIGN(count & SHIFT_MASK64);
    // If byte tags overlap, take the union of tag of the overlapping byte
    if(count % 8)
        *(UINT64 *)get_tag_address(dst) |= 
           tmp_tag >> (BYTE_ALIGN(count & SHIFT_MASK64) + BYTE_BITS);
    
    // if count is tainted, take the union of count's taint with each byte
    UINT8 count_tag = *(UINT8 *)&thread_ctx->vcpu.gpr[count_reg];
    for(UINT8 i = 0; i < BIT2BYTE(QWORD_BITS); i++)
        *(((UINT8 *)get_tag_address(dst)) + i)  |= count_tag;
    
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst: %lx taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(UINT64 *)get_tag_address(dst));
#endif
}

/*
 * @ dst: 64-bit memory operand
 * @ count: imm - number of bits to shift. Masked to  6 bits 
 */
VOID shiftr_m_imm_bits_2op64(thread_ctx_t *thread_ctx, ADDRINT dst, 
        UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(UINT64 *)get_tag_address(dst))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    
#endif
    UINT64 tmp_tag = *(UINT64 *)get_tag_address(dst);
    
    *(UINT64 *)get_tag_address(dst) = 
        tmp_tag >> BYTE_ALIGN(count & SHIFT_MASK64);
    // If byte tags overlap, take the union of tag of the overlapping byte
    if(count % 8)
        *(UINT64 *)get_tag_address(dst) |= 
           tmp_tag >> (BYTE_ALIGN(count & SHIFT_MASK64) + BYTE_BITS);
    
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst: %lx taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(UINT64 *)get_tag_address(dst));
#endif
}

/*
 * @ dst: 32-bit memory operand
 * @ count: cl reg - number of bits to shift. Masked to  6 bits 
 * @ count_reg: 8 bit register containting count (for taint)
 */
VOID shiftr_m_cl_bits_2op32(thread_ctx_t *thread_ctx, ADDRINT dst, 
        UINT64 count, UINT32 count_reg, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(UINT32 *)get_tag_address(dst))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    
#endif
    UINT32 tmp_tag = *(UINT32 *)get_tag_address(dst);
    
    *(UINT32 *)get_tag_address(dst) = 
        tmp_tag >> BYTE_ALIGN(count & SHIFT_MASK);
    // If byte tags overlap, take the union of tag of the overlapping byte
    if(count % 8)
        *(UINT32 *)get_tag_address(dst) |= 
            tmp_tag >> (BYTE_ALIGN(count & SHIFT_MASK) + BYTE_BITS);
    
    // if count is tainted, take the union of count's taint with each byte
    UINT8 count_tag = *(UINT8 *)&thread_ctx->vcpu.gpr[count_reg];
    for(UINT8 i = 0; i < BIT2BYTE(DWORD_BITS); i++)
        *(((UINT8 *)get_tag_address(dst)) + i)  |= count_tag;
    // Zero the upper 32 bits
    *(((UINT32 *)get_tag_address(dst)) + 1) = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst: %lx taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(UINT32 *)get_tag_address(dst));
#endif
}

/*
 * @ dst: 32-bit memory operand
 * @ count: imm - number of bits to shift. Masked to  6 bits 
 */
VOID shiftr_m_imm_bits_2op32(thread_ctx_t *thread_ctx, ADDRINT dst, 
        UINT64 count, UINT32 count_reg, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(UINT32 *)get_tag_address(dst))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    
#endif
    UINT32 tmp_tag = *(UINT32 *)get_tag_address(dst);
    
    *(UINT32 *)get_tag_address(dst) = 
        tmp_tag >> BYTE_ALIGN(count & SHIFT_MASK);
    // If byte tags overlap, take the union of tag of the overlapping byte
    if(count % 8)
        *(UINT32 *)get_tag_address(dst) |= 
            tmp_tag >> (BYTE_ALIGN(count & SHIFT_MASK) + BYTE_BITS);
    
    // Zero the upper 32 bits
    *(((UINT32 *)get_tag_address(dst)) + 1) = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst: %lx taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(UINT32 *)get_tag_address(dst));
#endif
}

/*
 * @ dst: 16-bit memory operand
 * @ count: cl reg - number of bits to shift. Masked to  6 bits 
 * @ count_reg: 8 bit register containting count (for taint)
 */
VOID shiftr_m_cl_bits_2op16(thread_ctx_t *thread_ctx, ADDRINT dst, 
        UINT64 count, UINT32 count_reg, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(UINT16 *)get_tag_address(dst))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    
#endif
    UINT16 tmp_tag = *(UINT16 *)get_tag_address(dst);
    
    *(UINT16 *)get_tag_address(dst) = 
        tmp_tag >> BYTE_ALIGN(count & SHIFT_MASK);
    // If byte tags overlap, take the union of tag of the overlapping byte
    if(count % 8)
        *(UINT16 *)get_tag_address(dst) |= 
            tmp_tag >> (BYTE_ALIGN(count & SHIFT_MASK) + BYTE_BITS);
    
    // if count is tainted, take the union of count's taint with each byte
    UINT8 count_tag = *(UINT8 *)&thread_ctx->vcpu.gpr[count_reg];
    for(UINT8 i = 0; i < BIT2BYTE(WORD_BITS); i++)
        *(((UINT8 *)get_tag_address(dst)) + i)  |= count_tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst: %lx taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(UINT16 *)get_tag_address(dst));
#endif
}

/*
 * @ dst: 16-bit memory operand
 * @ count: imm - number of bits to shift. Masked to  6 bits 
 */
VOID shiftr_m_imm_bits_2op16(thread_ctx_t *thread_ctx, ADDRINT dst, 
        UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(UINT16 *)get_tag_address(dst))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    
#endif
    UINT16 tmp_tag = *(UINT16 *)get_tag_address(dst);
    
    *(UINT16 *)get_tag_address(dst) = 
        tmp_tag >> BYTE_ALIGN(count & SHIFT_MASK);
    // If byte tags overlap, take the union of tag of the overlapping byte
    if(count % 8)
        *(UINT16 *)get_tag_address(dst) |= 
            tmp_tag >> (BYTE_ALIGN(count & SHIFT_MASK) + BYTE_BITS);
    
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst: %lx taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(UINT16 *)get_tag_address(dst));
#endif
}

/*
 * @ dst: 8-bit memory operand
 * @ count: cl reg - number of bits to shift. Masked to  6 bits 
 * @ count_reg: 8 bit register containting count (for taint)
 */
VOID shiftr_m_cl_bits_2op8(thread_ctx_t *thread_ctx, ADDRINT dst, 
        UINT64 count, UINT32 count_reg, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(UINT8 *)get_tag_address(dst))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    
#endif
    UINT8 tmp_tag = *(UINT8 *)get_tag_address(dst);
    
    *(UINT8 *)get_tag_address(dst) = 
        tmp_tag >> BYTE_ALIGN(count & SHIFT_MASK);
    // If byte tags overlap, take the union of tag of the overlapping byte
    if(count % 8)
        *(UINT8 *)get_tag_address(dst) |= 
            tmp_tag >> (BYTE_ALIGN(count & SHIFT_MASK) + BYTE_BITS);
    
    // if count is tainted, take the union of count's taint with each byte
    UINT8 count_tag = *(UINT8 *)&thread_ctx->vcpu.gpr[count_reg];
    *((UINT8 *)get_tag_address(dst))  |= count_tag;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst: %lx taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(UINT64 *)get_tag_address(dst));
#endif
}

/*
 * @ dst: 8-bit memory operand
 * @ count: imm - number of bits to shift. Masked to  6 bits 
 */
VOID shiftr_m_imm_bits_2op8(thread_ctx_t *thread_ctx, ADDRINT dst, 
        UINT64 count, UINT32 count_reg, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(UINT8 *)get_tag_address(dst))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    
#endif
    UINT8 tmp_tag = *(UINT8 *)get_tag_address(dst);
    
    *(UINT8 *)get_tag_address(dst) = 
        tmp_tag >> BYTE_ALIGN(count & SHIFT_MASK);
    // If byte tags overlap, take the union of tag of the overlapping byte
    if(count % 8)
        *(UINT8 *)get_tag_address(dst) |= 
            tmp_tag >> (BYTE_ALIGN(count & SHIFT_MASK) + BYTE_BITS);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst: %lx taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(UINT64 *)get_tag_address(dst));
#endif
}



/*
 * Shifts dst operand to left count bits and shifts in bits from the src
 * operand. The bits shifted in are the most significant (src_len - count)
 * bits. Since taints are tracked at the byte level, we byte align the taint  
 * tag bitshift. If the data bitshift results in byte taint tags overlapping 
 * byte-boundaries, we must take the union of the two byte taint tags. 
 *      if count % 8 == 0: // count is already byte-aligned shift
 *          t[dst] = (t[dst] << count) | (t[src] >> (len - count)
 *      else // overlapping byte taint tags
 *          t[dst] = 
 *              ((t[dst] << byte_align(count)) | 
 *                  (t[src] >> (len - byte_align(count)))) |
 *              ((t[dst] << (byte_align(count) + 1)) | 
 *                  ([src] >> (len - (byte_align(count) + 1))))
 * @ dst: 64-bit register
 * @ src: 64-bit register
 * @ count_arg: number of bits to shift. Masked to 5 bits.
 * @ reg_width: bit-size of the src register
 */
VOID shiftl_in_rr_bits_3op64(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src, UINT64 count_arg, UINT32 reg_width, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.gpr[dst])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst reg: %u - taint %lx "
                "src reg: %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.gpr[dst],
                src, thread_ctx->vcpu.gpr[src]);
#endif
    UINT64 dst_tag = thread_ctx->vcpu.gpr[dst];
    UINT64 src_tag = thread_ctx->vcpu.gpr[src];
    UINT32 count = count_arg % 64;

    // whole-byte shift
    if(count % 8 == 0)
        thread_ctx->vcpu.gpr[dst] = 
            (dst_tag << count) | (src_tag >> (reg_width - count));
    // Overlapping taint tag shift
    else
        thread_ctx->vcpu.gpr[dst] = 
            ((dst_tag << BYTE_ALIGN(count)) | 
                (src_tag >> (reg_width - BYTE_ALIGN(count)))) |
            ((dst_tag << (BYTE_ALIGN(count) + BYTE_BITS)) | 
                (src_tag >> (reg_width - (BYTE_ALIGN(count) + BYTE_BITS))));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst reg: %u - taint %lx "
                "src reg: %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.gpr[dst],
                src, thread_ctx->vcpu.gpr[src]);
#endif
}

/*
 * Shifts dst operand to left count bits and shifts in bits from the src
 * operand. The bits shifted in are the most significant (src_len - count)
 * bits. Since taints are tracked at the byte level, we byte align the taint  
 * tag bitshift. If the data bitshift results in byte taint tags overlapping 
 * byte-boundaries, we must take the union of the two byte taint tags. 
 *      if count % 8 == 0: // count is already byte-aligned shift
 *          t[dst] = (t[dst] << count) | (t[src] >> (len - count)
 *      else // overlapping byte taint tags
 *          t[dst] = 
 *              ((t[dst] << byte_align(count)) | 
 *                  (t[src] >> (len - byte_align(count)))) |
 *              ((t[dst] << (byte_align(count) + 1)) | 
 *                  ([src] >> (len - (byte_align(count) + 1))))
 * @ dst: 32-bit register
 * @ src: 32-bit register
 * @ count_arg: number of bits to shift. Masked to 4 bits.
 * @ reg_width: bit-size of the src register
 */
VOID shiftl_in_rr_bits_3op32(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src, UINT64 count_arg, UINT32 reg_width, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.gpr[dst])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst reg: %u - taint %lx "
                "src reg: %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.gpr[dst],
                src, thread_ctx->vcpu.gpr[src]);
#endif
    UINT32 dst_tag = *(UINT32 *)&thread_ctx->vcpu.gpr[dst];
    UINT32 src_tag = *(UINT32 *)&thread_ctx->vcpu.gpr[src];
    UINT32 count = count_arg % 32;

    // whole-byte shift
    if(count % 8 == 0)
        *(UINT32 *)&thread_ctx->vcpu.gpr[dst] = 
            (dst_tag << count) | (src_tag >> (reg_width - count));
    // Overlapping taint tag shift
    else
        *(UINT32 *)&thread_ctx->vcpu.gpr[dst] = 
            ((dst_tag << BYTE_ALIGN(count)) | 
                (src_tag >> (reg_width - BYTE_ALIGN(count)))) |
            ((dst_tag << (BYTE_ALIGN(count) + BYTE_BITS)) | 
                (src_tag >> (reg_width - (BYTE_ALIGN(count) + BYTE_BITS))));
    // zero the upper 32-bits
    *(((UINT32 *)&thread_ctx->vcpu.gpr[dst]) + 1) = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst reg: %u - taint %lx "
                "src reg: %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.gpr[dst],
                src, thread_ctx->vcpu.gpr[src]);
#endif
}

/*
 * Shifts dst operand to left count bits and shifts in bits from the src
 * operand. The bits shifted in are the most significant (src_len - count)
 * bits. Since taints are tracked at the byte level, we byte align the taint  
 * tag bitshift. If the data bitshift results in byte taint tags overlapping 
 * byte-boundaries, we must take the union of the two byte taint tags. 
 *      if count % 8 == 0: // count is already byte-aligned shift
 *          t[dst] = (t[dst] << count) | (t[src] >> (len - count)
 *      else // overlapping byte taint tags
 *          t[dst] = 
 *              ((t[dst] << byte_align(count)) | 
 *                  (t[src] >> (len - byte_align(count)))) |
 *              ((t[dst] << (byte_align(count) + 1)) | 
 *                  ([src] >> (len - (byte_align(count) + 1))))
 * @ dst: 16-bit register
 * @ src: 16-bit register
 * @ count_arg: number of bits to shift. Masked to 4 bits.
 * @ reg_width: bit-size of the src register
 */
VOID shiftl_in_rr_bits_3op16(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src, UINT64 count_arg, UINT32 reg_width, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(UINT16 *)&thread_ctx->vcpu.gpr[dst])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst reg: %u - taint %lx "
                "src reg: %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(UINT16 *)&thread_ctx->vcpu.gpr[dst],
                src, *(UINT16 *)&thread_ctx->vcpu.gpr[src]);
#endif
    UINT16 dst_tag = *(UINT16 *)&thread_ctx->vcpu.gpr[dst];
    UINT16 src_tag = *(UINT16 *)&thread_ctx->vcpu.gpr[src];
    UINT32 count = count_arg % 32;

    // whole-byte shift
    if(count % 8 == 0)
        *(UINT16 *)&thread_ctx->vcpu.gpr[dst] = 
            (dst_tag << count) | (src_tag >> (reg_width - count));
    // Overlapping taint tag shift
    else
        *(UINT16 *)&thread_ctx->vcpu.gpr[dst] = 
            ((dst_tag << BYTE_ALIGN(count)) | 
                (src_tag >> (reg_width - BYTE_ALIGN(count)))) |
            ((dst_tag << (BYTE_ALIGN(count) + BYTE_BITS)) | 
                (src_tag >> (reg_width - (BYTE_ALIGN(count) + BYTE_BITS))));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst reg: %u - taint %lx "
                "src reg: %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst,*(UINT16 *)&thread_ctx->vcpu.gpr[dst],
                src, *(UINT16 *)&thread_ctx->vcpu.gpr[src]);
#endif
}

/*
 * Shifts dst operand to left count bits and shifts in bits from the src
 * operand. The bits shifted in are the most significant (src_len - count)
 * bits. Since taints are tracked at the byte level, we byte align the taint  
 * tag bitshift. If the data bitshift results in byte taint tags overlapping 
 * byte-boundaries, we must take the union of the two byte taint tags. 
 *      if count % 8 == 0: // count is already byte-aligned shift
 *          t[dst] = (t[dst] << count) | (t[src] >> (len - count)
 *      else // overlapping byte taint tags
 *          t[dst] = 
 *              ((t[dst] << byte_align(count)) | 
 *                  (t[src] >> (len - byte_align(count)))) |
 *              ((t[dst] << (byte_align(count) + 1)) | 
 *                  ([src] >> (len - (byte_align(count) + 1))))
 * @ dst: 64-bit memory location
 * @ src: 64-bit register
 * @ count_arg: number of bits to shift. Masked to 5 bits.
 * @ reg_width: bit-size of the src register
 */
VOID shiftl_in_mr_bits_3op64(thread_ctx_t *thread_ctx, ADDRINT dst, 
        UINT32 src, UINT64 count_arg, UINT32 reg_width, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(UINT64 *)get_tag_address(dst))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst: 0x%lx - taint %lx "
                "src reg: %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(UINT64 *)get_tag_address(dst),
                src, thread_ctx->vcpu.gpr[src]);
#endif
    UINT64 dst_tag = *(UINT64 *)get_tag_address(dst);
    UINT64 src_tag = thread_ctx->vcpu.gpr[src];
    UINT32 count = count_arg % 64;

    // whole-byte shift
    if(count % 8 == 0)
        *(UINT64 *)get_tag_address(dst) = 
            (dst_tag << count) | (src_tag >> (reg_width - count));
    // Overlapping taint tag shift
    else
        *(UINT64 *)get_tag_address(dst) = 
            ((dst_tag << BYTE_ALIGN(count)) | 
                (src_tag >> (reg_width - BYTE_ALIGN(count)))) |
            ((dst_tag << (BYTE_ALIGN(count) + BYTE_BITS)) | 
                (src_tag >> (reg_width - (BYTE_ALIGN(count) + BYTE_BITS))));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst: 0x%lx - taint %lx "
                "src reg: %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(UINT64 *)get_tag_address(dst),
                src, thread_ctx->vcpu.gpr[src]);
#endif
}

/*
 * Shifts dst operand to left count bits and shifts in bits from the src
 * operand. The bits shifted in are the most significant (src_len - count)
 * bits. Since taints are tracked at the byte level, we byte align the taint  
 * tag bitshift. If the data bitshift results in byte taint tags overlapping 
 * byte-boundaries, we must take the union of the two byte taint tags. 
 *      if count % 8 == 0: // count is already byte-aligned shift
 *          t[dst] = (t[dst] << count) | (t[src] >> (len - count)
 *      else // overlapping byte taint tags
 *          t[dst] = 
 *              ((t[dst] << byte_align(count)) | 
 *                  (t[src] >> (len - byte_align(count)))) |
 *              ((t[dst] << (byte_align(count) + 1)) | 
 *                  ([src] >> (len - (byte_align(count) + 1))))
 * @ dst: 32-bit memory location
 * @ src: 32-bit register
 * @ count_arg: number of bits to shift. Masked to 5 bits.
 * @ reg_width: bit-size of the src register
 */
VOID shiftl_in_mr_bits_3op32(thread_ctx_t *thread_ctx, ADDRINT dst, 
        UINT32 src, UINT64 count_arg, UINT32 reg_width, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(UINT32 *)get_tag_address(dst))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst: 0x%lx - taint %lx "
                "src reg: %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(UINT32 *)get_tag_address(dst),
                src, thread_ctx->vcpu.gpr[src]);
#endif
    UINT32 dst_tag = *(UINT32 *)get_tag_address(dst);
    UINT32 src_tag = thread_ctx->vcpu.gpr[src];
    UINT32 count = count_arg % 32;

    // whole-byte shift
    if(count % 8 == 0)
        *(UINT32 *)get_tag_address(dst) = 
            (dst_tag << count) | (src_tag >> (reg_width - count));
    // Overlapping taint tag shift
    else
        *(UINT32 *)get_tag_address(dst) = 
            ((dst_tag << BYTE_ALIGN(count)) | 
                (src_tag >> (reg_width - BYTE_ALIGN(count)))) |
            ((dst_tag << (BYTE_ALIGN(count) + BYTE_BITS)) | 
                (src_tag >> (reg_width - (BYTE_ALIGN(count) + BYTE_BITS))));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst: 0x%lx - taint %lx "
                "src reg: %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(UINT32 *)get_tag_address(dst),
                src, thread_ctx->vcpu.gpr[src]);
#endif
}

/*
 * Shifts dst operand to left count bits and shifts in bits from the src
 * operand. The bits shifted in are the most significant (src_len - count)
 * bits. Since taints are tracked at the byte level, we byte align the taint  
 * tag bitshift. If the data bitshift results in byte taint tags overlapping 
 * byte-boundaries, we must take the union of the two byte taint tags. 
 *      if count % 8 == 0: // count is already byte-aligned shift
 *          t[dst] = (t[dst] << count) | (t[src] >> (len - count)
 *      else // overlapping byte taint tags
 *          t[dst] = 
 *              ((t[dst] << byte_align(count)) | 
 *                  (t[src] >> (len - byte_align(count)))) |
 *              ((t[dst] << (byte_align(count) + 1)) | 
 *                  ([src] >> (len - (byte_align(count) + 1))))
 * @ dst: 16-bit memory location
 * @ src: 16-bit register
 * @ count_arg: number of bits to shift. Masked to 5 bits.
 * @ reg_width: bit-size of the src register
 */
VOID shiftl_in_mr_bits_3op16(thread_ctx_t *thread_ctx, ADDRINT dst, 
        UINT32 src, UINT64 count_arg, UINT32 reg_width, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(UINT16 *)get_tag_address(dst))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst: 0x%lx - taint %lx "
                "src reg: %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(UINT16 *)get_tag_address(dst),
                src, thread_ctx->vcpu.gpr[src]);
#endif
    UINT16 dst_tag = *(UINT16 *)get_tag_address(dst);
    UINT16 src_tag = thread_ctx->vcpu.gpr[src];
    UINT32 count = count_arg % 32;

    // whole-byte shift
    if(count % 8 == 0)
        *(UINT16 *)get_tag_address(dst) = 
            (dst_tag << count) | (src_tag >> (reg_width - count));
    // Overlapping taint tag shift
    else
        *(UINT16 *)get_tag_address(dst) = 
            ((dst_tag << BYTE_ALIGN(count)) | 
                (src_tag >> (reg_width - BYTE_ALIGN(count)))) |
            ((dst_tag << (BYTE_ALIGN(count) + BYTE_BITS)) | 
                (src_tag >> (reg_width - (BYTE_ALIGN(count) + BYTE_BITS))));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst: 0x%lx - taint %lx "
                "src reg: %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(UINT16 *)get_tag_address(dst),
                src, thread_ctx->vcpu.gpr[src]);
#endif
}


/*
 * Shifts dst operand to right count bits and shifts in bits from the src
 * operand. The bits shifted in are the least significant (src_len - count)
 * bits. Since taints are tracked at the byte level, we byte align the taint  
 * tag bitshift. If the data bitshift results in byte taint tags overlapping 
 * byte-boundaries, we must take the union of the two byte taint tags. 
 *      if count % 8 == 0: // count is already byte-aligned shift
 *          t[dst] = (t[dst] >> count) | (t[src] << (len - count)
 *      else // overlapping byte taint tags
 *          t[dst] = 
 *              ((t[dst] >> byte_align(count)) | 
 *                  (t[src] << (len - byte_align(count)))) |
 *              ((t[dst] >> (byte_align(count) + 1)) | 
 *                  ([src] << (len - (byte_align(count) + 1))))
 * @ dst: 64-bit register
 * @ src: 64-bit register
 * @ count_arg: number of bits to shift. Masked to 5 bits.
 * @ reg_width: bit-size of the src register
 */
VOID shiftr_in_rr_bits_3op64(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src, UINT64 count_arg, UINT32 reg_width, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.gpr[dst] || thread_ctx->vcpu.gpr[src])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst reg: %u - taint %lx "
                "src reg: %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.gpr[dst],
                src, thread_ctx->vcpu.gpr[src]);
#endif
    UINT64 dst_tag = thread_ctx->vcpu.gpr[dst];
    UINT64 src_tag = thread_ctx->vcpu.gpr[src];
    UINT32 count = count_arg % 64;

    // whole-byte shift
    if(count % 8 == 0)
        thread_ctx->vcpu.gpr[dst] = 
            (dst_tag >> count) | (src_tag << (reg_width - count));
    // Overlapping taint tag shift
    else
        thread_ctx->vcpu.gpr[dst] = 
            ((dst_tag >> BYTE_ALIGN(count)) | 
                (src_tag << (reg_width - BYTE_ALIGN(count)))) |
            ((dst_tag >> (BYTE_ALIGN(count) + BYTE_BITS)) | 
                (src_tag << (reg_width - (BYTE_ALIGN(count) + BYTE_BITS))));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst reg: %u - taint %lx "
                "src reg: %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.gpr[dst],
                src, thread_ctx->vcpu.gpr[src]);
#endif
}

/*
 * Shifts dst operand to right count bits and shifts in bits from the src
 * operand. The bits shifted in are the least significant (src_len - count)
 * bits. Since taints are tracked at the byte level, we byte align the taint  
 * tag bitshift. If the data bitshift results in byte taint tags overlapping 
 * byte-boundaries, we must take the union of the two byte taint tags. 
 *      if count % 8 == 0: // count is already byte-aligned shift
 *          t[dst] = (t[dst] >> count) | (t[src] << (len - count)
 *      else // overlapping byte taint tags
 *          t[dst] = 
 *              ((t[dst] >> byte_align(count)) | 
 *                  (t[src] << (len - byte_align(count)))) |
 *              ((t[dst] >> (byte_align(count) + 1)) | 
 *                  ([src] << (len - (byte_align(count) + 1))))
 * @ dst: 32-bit register
 * @ src: 32-bit register
 * @ count_arg: number of bits to shift. Masked to 4 bits.
 * @ reg_width: bit-size of the src register
 */
VOID shiftr_in_rr_bits_3op32(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src, UINT64 count_arg, UINT32 reg_width, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.gpr[dst])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst reg: %u - taint %lx "
                "src reg: %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.gpr[dst],
                src, thread_ctx->vcpu.gpr[src]);
#endif
    UINT32 dst_tag = *(UINT32 *)&thread_ctx->vcpu.gpr[dst];
    UINT32 src_tag = *(UINT32 *)&thread_ctx->vcpu.gpr[src];
    UINT32 count = count_arg % 32;

    // whole-byte shift
    if(count % 8 == 0)
    {
        *(UINT32 *)&thread_ctx->vcpu.gpr[dst] = 
            (dst_tag >> count) | (src_tag << (reg_width - count));
    }
    // Overlapping taint tag shift
    else
    {
        *(UINT32 *)&thread_ctx->vcpu.gpr[dst] = 
            ((dst_tag >> BYTE_ALIGN(count)) | 
                (src_tag << (reg_width - BYTE_ALIGN(count)))) |
            ((dst_tag >> (BYTE_ALIGN(count) + BYTE_BITS)) | 
                (src_tag << (reg_width - (BYTE_ALIGN(count) + BYTE_BITS))));
    }
    // zero the upper 32-bits
    *(((UINT32 *)&thread_ctx->vcpu.gpr[dst]) + 1) = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst reg: %u - taint %lx "
                "src reg: %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.gpr[dst],
                src, thread_ctx->vcpu.gpr[src]);
#endif
}

/*
 * Shifts dst operand to right count bits and shifts in bits from the src
 * operand. The bits shifted in are the least significant (src_len - count)
 * bits. Since taints are tracked at the byte level, we byte align the taint  
 * tag bitshift. If the data bitshift results in byte taint tags overlapping 
 * byte-boundaries, we must take the union of the two byte taint tags. 
 *      if count % 8 == 0: // count is already byte-aligned shift
 *          t[dst] = (t[dst] >> count) | (t[src] << (len - count)
 *      else // overlapping byte taint tags
 *          t[dst] = 
 *              ((t[dst] >> byte_align(count)) | 
 *                  (t[src] << (len - byte_align(count)))) |
 *              ((t[dst] >> (byte_align(count) + 1)) | 
 *                  ([src] << (len - (byte_align(count) + 1))))
 * @ dst: 16-bit register
 * @ src: 16-bit register
 * @ count_arg: number of bits to shift. Masked to 4 bits.
 * @ reg_width: bit-size of the src register
 */
VOID shiftr_in_rr_bits_3op16(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src, UINT64 count_arg, UINT32 reg_width, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(UINT16 *)&thread_ctx->vcpu.gpr[dst])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst reg: %u - taint %lx "
                "src reg: %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(UINT16 *)&thread_ctx->vcpu.gpr[dst],
                src, *(UINT16 *)&thread_ctx->vcpu.gpr[src]);
#endif
    UINT16 dst_tag = *(UINT16 *)&thread_ctx->vcpu.gpr[dst];
    UINT16 src_tag = *(UINT16 *)&thread_ctx->vcpu.gpr[src];
    UINT32 count = count_arg % 32;

    // whole-byte shift
    if(count % 8 == 0)
        *(UINT16 *)&thread_ctx->vcpu.gpr[dst] = 
            (dst_tag >> count) | (src_tag << (reg_width - count));
    // Overlapping taint tag shift
    else
        *(UINT16 *)&thread_ctx->vcpu.gpr[dst] = 
            ((dst_tag >> BYTE_ALIGN(count)) | 
                (src_tag << (reg_width - BYTE_ALIGN(count)))) |
            ((dst_tag >> (BYTE_ALIGN(count) + BYTE_BITS)) | 
                (src_tag << (reg_width - (BYTE_ALIGN(count) + BYTE_BITS))));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst reg: %u - taint %lx "
                "src reg: %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst,*(UINT16 *)&thread_ctx->vcpu.gpr[dst],
                src, *(UINT16 *)&thread_ctx->vcpu.gpr[src]);
#endif
}

/*
 * Shifts dst operand to right count bits and shifts in bits from the src
 * operand. The bits shifted in are the least significant (src_len - count)
 * bits. Since taints are tracked at the byte level, we byte align the taint  
 * tag bitshift. If the data bitshift results in byte taint tags overlapping 
 * byte-boundaries, we must take the union of the two byte taint tags. 
 *      if count % 8 == 0: // count is already byte-aligned shift
 *          t[dst] = (t[dst] >> count) | (t[src] << (len - count)
 *      else // overlapping byte taint tags
 *          t[dst] = 
 *              ((t[dst] >> byte_align(count)) | 
 *                  (t[src] << (len - byte_align(count)))) |
 *              ((t[dst] >> (byte_align(count) + 1)) | 
 *                  ([src] << (len - (byte_align(count) + 1))))
 * @ dst: 64-bit memory location
 * @ src: 64-bit register
 * @ count_arg: number of bits to shift. Masked to 5 bits.
 * @ reg_width: bit-size of the src register
 */
VOID shiftr_in_mr_bits_3op64(thread_ctx_t *thread_ctx, ADDRINT dst, 
        UINT32 src, UINT64 count_arg, UINT32 reg_width, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(UINT64 *)get_tag_address(dst))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst: 0x%lx - taint %lx "
                "src reg: %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(UINT64 *)get_tag_address(dst),
                src, thread_ctx->vcpu.gpr[src]);
#endif
    UINT64 dst_tag = *(UINT64 *)get_tag_address(dst);
    UINT64 src_tag = thread_ctx->vcpu.gpr[src];
    UINT32 count = count_arg % 64;

    // whole-byte shift
    if(count % 8 == 0)
        *(UINT64 *)get_tag_address(dst) = 
            (dst_tag >> count) | (src_tag << (reg_width - count));
    // Overlapping taint tag shift
    else
        *(UINT64 *)get_tag_address(dst) = 
            ((dst_tag >> BYTE_ALIGN(count)) | 
                (src_tag << (reg_width - BYTE_ALIGN(count)))) |
            ((dst_tag >> (BYTE_ALIGN(count) + BYTE_BITS)) | 
                (src_tag << (reg_width - (BYTE_ALIGN(count) + BYTE_BITS))));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst: 0x%lx - taint %lx "
                "src reg: %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(UINT64 *)get_tag_address(dst),
                src, thread_ctx->vcpu.gpr[src]);
#endif
}

/*
 * Shifts dst operand to right count bits and shifts in bits from the src
 * operand. The bits shifted in are the least significant (src_len - count)
 * bits. Since taints are tracked at the byte level, we byte align the taint  
 * tag bitshift. If the data bitshift results in byte taint tags overlapping 
 * byte-boundaries, we must take the union of the two byte taint tags. 
 *      if count % 8 == 0: // count is already byte-aligned shift
 *          t[dst] = (t[dst] >> count) | (t[src] << (len - count)
 *      else // overlapping byte taint tags
 *          t[dst] = 
 *              ((t[dst] >> byte_align(count)) | 
 *                  (t[src] << (len - byte_align(count)))) |
 *              ((t[dst] >> (byte_align(count) + 1)) | 
 *                  ([src] << (len - (byte_align(count) + 1))))
 * @ dst: 32-bit memory location
 * @ src: 32-bit register
 * @ count_arg: number of bits to shift. Masked to 5 bits.
 * @ reg_width: bit-size of the src register
 */
VOID shiftr_in_mr_bits_3op32(thread_ctx_t *thread_ctx, ADDRINT dst, 
        UINT32 src, UINT64 count_arg, UINT32 reg_width, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(UINT32 *)get_tag_address(dst))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst: 0x%lx - taint %lx "
                "src reg: %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(UINT32 *)get_tag_address(dst),
                src, thread_ctx->vcpu.gpr[src]);
#endif
    UINT32 dst_tag = *(UINT32 *)get_tag_address(dst);
    UINT32 src_tag = thread_ctx->vcpu.gpr[src];
    UINT32 count = count_arg % 32;

    // whole-byte shift
    if(count % 8 == 0)
        *(UINT32 *)get_tag_address(dst) = 
            (dst_tag >> count) | (src_tag << (reg_width - count));
    // Overlapping taint tag shift
    else
        *(UINT32 *)get_tag_address(dst) = 
            ((dst_tag >> BYTE_ALIGN(count)) | 
                (src_tag << (reg_width - BYTE_ALIGN(count)))) |
            ((dst_tag >> (BYTE_ALIGN(count) + BYTE_BITS)) | 
                (src_tag << (reg_width - (BYTE_ALIGN(count) + BYTE_BITS))));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst: 0x%lx - taint %lx "
                "src reg: %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(UINT32 *)get_tag_address(dst),
                src, thread_ctx->vcpu.gpr[src]);
#endif
}

/*
 * Shifts dst operand to right count bits and shifts in bits from the src
 * operand. The bits shifted in are the least significant (src_len - count)
 * bits. Since taints are tracked at the byte level, we byte align the taint  
 * tag bitshift. If the data bitshift results in byte taint tags overlapping 
 * byte-boundaries, we must take the union of the two byte taint tags. 
 *      if count % 8 == 0: // count is already byte-aligned shift
 *          t[dst] = (t[dst] >> count) | (t[src] << (len - count)
 *      else // overlapping byte taint tags
 *          t[dst] = 
 *              ((t[dst] >> byte_align(count)) | 
 *                  (t[src] << (len - byte_align(count)))) |
 *              ((t[dst] >> (byte_align(count) + 1)) | 
 *                  ([src] << (len - (byte_align(count) + 1))))
 * @ dst: 16-bit memory location
 * @ src: 16-bit register
 * @ count_arg: number of bits to shift. Masked to 5 bits.
 * @ reg_width: bit-size of the src register
 */
VOID shiftr_in_mr_bits_3op16(thread_ctx_t *thread_ctx, ADDRINT dst, 
        UINT32 src, UINT64 count_arg, UINT32 reg_width, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(UINT16 *)get_tag_address(dst))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst: 0x%lx - taint %lx "
                "src reg: %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(UINT16 *)get_tag_address(dst),
                src, thread_ctx->vcpu.gpr[src]);
#endif
    UINT16 dst_tag = *(UINT16 *)get_tag_address(dst);
    UINT16 src_tag = thread_ctx->vcpu.gpr[src];
    UINT32 count = count_arg % 32;

    // whole-byte shift
    if(count % 8 == 0)
        *(UINT16 *)get_tag_address(dst) = 
            (dst_tag >> count) | (src_tag << (reg_width - count));
    // Overlapping taint tag shift
    else
        *(UINT16 *)get_tag_address(dst) = 
            ((dst_tag >> BYTE_ALIGN(count)) | 
                (src_tag << (reg_width - BYTE_ALIGN(count)))) |
            ((dst_tag >> (BYTE_ALIGN(count) + BYTE_BITS)) | 
                (src_tag << (reg_width - (BYTE_ALIGN(count) + BYTE_BITS))));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst: 0x%lx - taint %lx "
                "src reg: %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(UINT16 *)get_tag_address(dst),
                src, thread_ctx->vcpu.gpr[src]);
#endif
}








VOID unhandled_mem_read(VOID *addr, UINT32 num, UINT32 opcode)
{
    printLog("unhandled mem read in %s at %ld of %u bytes \n", 
            OPCODE_StringShort(opcode).c_str(), addr, num);
    if(mem_is_tainted((ADDRINT)addr, num))
        printLog("unhandled mem read: %s: %u bytes at addr %lx tainted %u\n",  
            OPCODE_StringShort(opcode).c_str(), 
            num, addr, mem_is_tainted((ADDRINT)addr, num));
}


// New instruction analysis functions////////////////////////
// rotate instructions

VOID rotatel_r_bits_2op64(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT64 count, UINT32 count_is_reg, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.gpr[dst] || 
            (count_is_reg && *(UINT8 *)&thread_ctx->vcpu.gpr[RCX]))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst reg: %u - taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
    UINT64 tmp_tag = thread_ctx->vcpu.gpr[dst];
    
    thread_ctx->vcpu.gpr[dst] = 
        (tmp_tag << BYTE_ALIGN(count & SHIFT_MASK64)) |
        (tmp_tag >> (64 - BYTE_ALIGN(count & SHIFT_MASK64)));
   // If byte tags overlap, take the union of tag of the overlapping byte
   if(count % 8)
       thread_ctx->vcpu.gpr[dst] |= 
        (tmp_tag << (BYTE_ALIGN(count & SHIFT_MASK64) + BYTE_BITS)) |
        (tmp_tag >> (64 - (BYTE_ALIGN(count & SHIFT_MASK64) + BYTE_BITS)));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst reg: %u - taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
}

VOID rotatel_r_bits_2op32(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT64 count, UINT32 count_is_reg, UINT32 opcode)
{
    if(thread_ctx->vcpu.gpr[dst] || 
            (count_is_reg && *(UINT8 *)&thread_ctx->vcpu.gpr[RCX]))
        printLog("%s r32 TOUCHES TAINTED DATA\n", 
                OPCODE_StringShort(opcode).c_str());
}

VOID rotatel_r_bits_2op16(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT64 count, UINT32 count_is_reg, UINT32 opcode)
{
    if(*(UINT16 *)&thread_ctx->vcpu.gpr[dst] || 
            (count_is_reg && *(UINT8 *)&thread_ctx->vcpu.gpr[RCX]))
        printLog("%s r16 TOUCHES TAINTED DATA\n", 
                OPCODE_StringShort(opcode).c_str());
}

VOID rotatel_r_bits_2op8l(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT64 count, UINT32 count_is_reg, UINT32 opcode)
{
    if(*(UINT8 *)&thread_ctx->vcpu.gpr[dst] || 
            (count_is_reg && *(UINT8 *)&thread_ctx->vcpu.gpr[RCX]))
        printLog("%s r8l TOUCHES TAINTED DATA\n", 
                OPCODE_StringShort(opcode).c_str());
}

VOID rotatel_r_bits_2op8u(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT64 count, UINT32 count_is_reg, UINT32 opcode)
{
    if(*(((UINT8 *)&thread_ctx->vcpu.gpr[dst]) + 1) || 
            (count_is_reg && *(UINT8 *)&thread_ctx->vcpu.gpr[RCX]))
        printLog("%s r8u TOUCHES TAINTED DATA\n", 
                OPCODE_StringShort(opcode).c_str());
}

VOID rotatel_m_bits_2op64(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT64 count, UINT32 count_is_reg, UINT32 opcode)
{
    if(*(UINT64 *)&thread_ctx->vcpu.gpr[dst] || 
            (count_is_reg && *(UINT8 *)&thread_ctx->vcpu.gpr[RCX]))
        printLog("%s m64 TOUCHES TAINTED DATA\n", 
                OPCODE_StringShort(opcode).c_str());
}

VOID rotatel_m_bits_2op32(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT64 count, UINT32 count_is_reg, UINT32 opcode)
{
    if(*(UINT32 *)&thread_ctx->vcpu.gpr[dst] || 
            (count_is_reg && *(UINT8 *)&thread_ctx->vcpu.gpr[RCX]))
        printLog("%s m32 TOUCHES TAINTED DATA\n", 
                OPCODE_StringShort(opcode).c_str());
}

VOID rotatel_m_bits_2op16(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT64 count, UINT32 count_is_reg, UINT32 opcode)
{
    if(*(UINT16 *)&thread_ctx->vcpu.gpr[dst] || 
            (count_is_reg && *(UINT8 *)&thread_ctx->vcpu.gpr[RCX]))
        printLog("%s m16 TOUCHES TAINTED DATA\n", 
                OPCODE_StringShort(opcode).c_str());
}

VOID rotatel_m_bits_2op8(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT64 count, UINT32 count_is_reg, UINT32 opcode)
{
    if(*(UINT8 *)&thread_ctx->vcpu.gpr[dst] || 
            (count_is_reg && *(UINT8 *)&thread_ctx->vcpu.gpr[RCX]))
        printLog("%s m8 TOUCHES TAINTED DATA\n", 
                OPCODE_StringShort(opcode).c_str());
}

VOID alignr_xmm_2op128(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src, UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[src][0])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx "
                "src xmm: %u  taint %lx taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                src, thread_ctx->vcpu.avx[src][0]);
#endif
    // Since we're only using the low 128 bits, ignore the upper
    uint128_t tmp_tag =
        (thread_ctx->vcpu.avx[dst][0] >> (BIT2BYTE(count))) |
        ((*(uint128_t *)&thread_ctx->vcpu.avx[src]) << 
         (XMM_BITS - BIT2BYTE(count)));
   thread_ctx->vcpu.avx[dst][0] = tmp_tag; 
#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 2, POST,  XMM, dst, XMM, src);
#endif
}

VOID alignr_m_2op128(thread_ctx_t *thread_ctx, UINT32 dst, 
        ADDRINT src, UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || *(uint128_t *)get_tag_address(src))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx "
                "src: 0x%lx taint %lx taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                src, *(uint128_t *)get_tag_address(src));
#endif
    // Since we're only using the low 128 bits, ignore the upper
    uint128_t tmp_tag =
        (thread_ctx->vcpu.avx[dst][0] >> (BIT2BYTE(count))) |
        (*(uint128_t *)get_tag_address(src) << (XMM_BITS - BIT2BYTE(count)));
   thread_ctx->vcpu.avx[dst][0] = tmp_tag; 
#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 2, POST,  XMM, dst, M128, src);
#endif
}

VOID alignr_xmm_xmm_3op128(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src1, UINT32 src2, UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[src1][0] || 
            thread_ctx->vcpu.avx[src2][0])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx "
                "src1 xmm %u taint %lx src2 xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                src1, thread_ctx->vcpu.avx[src1][0],
                src2, thread_ctx->vcpu.avx[src2][0]);
#endif
    // Since we're only using the low 128 bits, ignore the upper
    thread_ctx->vcpu.avx[dst][0] = 
        (thread_ctx->vcpu.avx[src2][0] >> (BIT2BYTE(count))) |
        (thread_ctx->vcpu.avx[src1][0] << (XMM_BITS - BIT2BYTE(count)));

    //zero the upper 128 bits
    thread_ctx->vcpu.avx[dst][1] = TAG_ZERO; 
#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 3, POST,  XMM, dst, XMM, src1, XMM, src2);
#endif
}

VOID alignr_xmm_m_3op128(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src1, ADDRINT src2, UINT64 count, UINT32 opcode)
{
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[src1][0] ||
            *(uint128_t *)get_tag_address(src2))
        printLog("%s xmm m TOUCHES TAINTED DATA\n", 
                OPCODE_StringShort(opcode).c_str());
}

VOID alignr_ymm_ymm_3op256(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src1, UINT32 src2, UINT64 count, UINT32 opcode)
{
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1]|| 
            thread_ctx->vcpu.avx[src1][0] || thread_ctx->vcpu.avx[src1][1] ||
            thread_ctx->vcpu.avx[src2][0] || thread_ctx->vcpu.avx[src2][1])
        printLog("%s ymm ymm TOUCHES TAINTED DATA\n", 
                OPCODE_StringShort(opcode).c_str());
}

VOID alignr_ymm_m_3op256(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src1, ADDRINT src2, UINT64 count, UINT32 opcode)
{
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1]|| 
            thread_ctx->vcpu.avx[src1][0] || thread_ctx->vcpu.avx[src1][1] ||
            *(uint128_t *)get_tag_address(src2) || 
            *(((uint128_t *)get_tag_address(src2)) + 1))
        printLog("%s ymm m TOUCHES TAINTED DATA\n", 
                OPCODE_StringShort(opcode).c_str());
}





// xmm registers //////////////////////////////////////////////////////////////

/* Propagate taint from 128 bit XMM register to another XMM 
 * register with form:
 *      t[dst] = t[src]
 * Legacy SSE version: the upper 128 bits are not modified
 * @ src: XMM reg
 * @ dst: XMM reg
 */

VOID xmm2xmm_xfer_2op128(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(uint128_t *)&thread_ctx->vcpu.avx[src] || 
            *(uint128_t *)&thread_ctx->vcpu.avx[dst])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src xmm: %u - taint %lu \
                dst xmm: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(uint128_t *)&thread_ctx->vcpu.avx[src],
                dst, *(uint128_t *)&thread_ctx->vcpu.avx[dst]);
#endif
	thread_ctx->vcpu.avx[dst][0] = thread_ctx->vcpu.avx[src][0];
#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 2, POST,  XMM, dst, XMM, src);
#endif
}

/* Propagate taint from 128 bit XMM register to another XMM 
 * register with form:
 *      t[dst] = t[src]
 * AVX version: zero upper 128 bits of dst XMM register
 * @ src: XMM reg
 * @ dst: XMM reg
 */

VOID xmm2xmm_xfer_2op128_zero_upper(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(uint128_t *)&thread_ctx->vcpu.avx[src] || *(uint128_t *)&thread_ctx->vcpu.avx[dst])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src xmm %u taint %lx "
                "dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(uint128_t *)&thread_ctx->vcpu.avx[src],
                dst, *(uint128_t *)&thread_ctx->vcpu.avx[dst]);
#endif
	thread_ctx->vcpu.avx[dst][0] = thread_ctx->vcpu.avx[src][0];
    // Xero upper 128 bits
    thread_ctx->vcpu.avx[dst][1] = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 2, POST,  XMM, dst, XMM, src);
#endif
}

/* Propagate taint from 128 bit memory location to another XMM 
 * register with form:
 *      t[dst] = t[src]
 * Legacy SSE version: the upper 128 bits are not modified
 * @ src: 128-bit memory location
 * @ dst: XMM reg
 */

VOID m2xmm_xfer_2op128(thread_ctx_t *thread_ctx, UINT32 dst, 
        ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(uint128_t *)get_tag_address(src) || 
            *(uint128_t *)&thread_ctx->vcpu.avx[dst])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: 0x%lx - taint %lu "
                "dst xmm: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(uint128_t *)get_tag_address(src),
                dst, *(uint128_t *)&thread_ctx->vcpu.avx[dst]);
#endif
    thread_ctx->vcpu.avx[dst][0] =
        *(uint128_t *)get_tag_address(src);
#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 2, POST,  XMM, dst, M128, src);
#endif
}

/* Propagate taint from 128 bit memory location to another XMM 
 * register with form:
 *      t[dst] = t[src]
 * AVX version: zero upper 128 bits of dst XMM register
 * @ src: 128-bit memory location
 * @ dst: XMM reg
 */

VOID m2xmm_xfer_2op128_zero_upper(thread_ctx_t *thread_ctx, UINT32 dst, 
        ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(uint128_t *)get_tag_address(src) || 
            *(uint128_t *)&thread_ctx->vcpu.avx[dst])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint %lu "
                "dst xmm: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(uint128_t *)get_tag_address(src),
                dst, *(uint128_t *)&thread_ctx->vcpu.avx[dst]);
#endif
	thread_ctx->vcpu.avx[dst][0] = *(uint128_t *)get_tag_address(src);
    
    // zero upper 128 bits of dst
    thread_ctx->vcpu.avx[dst][1] = TAG_ZERO; 
#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 2, POST,  XMM, dst, M128, src);
#endif
}


/* Propagate taint from an XMM register to a 128-bit memory location
 * register with form:
 *      t[dst] = t[src]
 * @ src: 128-bit memory location
 * @ dst: XMM reg
 */

VOID xmm2m_xfer_2op128(thread_ctx_t *thread_ctx, ADDRINT dst, 
        UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(uint128_t *)get_tag_address(dst) || 
            *((uint128_t *)&thread_ctx->vcpu.avx[src]))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src xmm reg: %u - taint %lu "
                "dst: %lx - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(uint128_t *)&thread_ctx->vcpu.avx[src],
                dst,  *(uint128_t *)get_tag_address(dst));
#endif
    //uint128_t taint = *(uint128_t *)&thread_ctx->vcpu.avx[src];
    //*(uint128_t *)get_tag_address(dst) = taint;
    *(uint128_t *)get_tag_address(dst)  = *(uint128_t *)&thread_ctx->vcpu.avx[src];
#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 2, POST,  M128, dst, XMM, src);
#endif
}

/* Propagate taint from 128 bit XMM register to another XMM 
 * register with form:
 *      t[dst] |= t[src]
 *  Legacy SSE version: the upper 128 bits are not modified
 * @ src: XMM reg
 * @ dst: XMM reg
 */

VOID xmm2xmm_union_2op128(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(uint128_t *)&thread_ctx->vcpu.avx[src] || 
            *(uint128_t *)&thread_ctx->vcpu.avx[dst])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src xmm: %u - taint %lu \
                dst xmm: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(uint128_t *)&thread_ctx->vcpu.avx[src],
                dst, *(uint128_t *)&thread_ctx->vcpu.avx[dst]);
#endif
	*(uint128_t *)&thread_ctx->vcpu.avx[dst] |= 
        *(uint128_t *)&thread_ctx->vcpu.avx[src];
#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 2, POST,  XMM, dst, XMM, src);
#endif
}

/* Propagate taint from 128 bit memory location to another XMM 
 * register with form:
 *      t[dst] |= t[src]
 * Legacy SSE version: the upper 128 bits are not modified
 * @ src: 128-bit memory location
 * @ dst: XMM reg
 */

VOID m2xmm_union_2op128(thread_ctx_t *thread_ctx, UINT32 dst, 
        ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(uint128_t *)get_tag_address(src) || *(uint128_t *)&thread_ctx->vcpu.avx[dst])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint %lu \
                dst xmm: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(uint128_t *)get_tag_address(src),
                dst, *(uint128_t *)&thread_ctx->vcpu.avx[dst]);
#endif

	*(uint128_t *)&thread_ctx->vcpu.avx[dst] |= 
        *(uint128_t *)get_tag_address(src);
#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 2, POST,  XMM, dst, M128, src);
#endif
}


/* Propagate taint from an XMM register to a 128-bit memory location
 * register with form:
 *      t[dst] |= t[src]
 * Legacy SSE version: the upper 128 bits are not modified
 * @ src: 128-bit memory location
 * @ dst: XMM reg
 */

VOID xmm2m_union_2op128(thread_ctx_t *thread_ctx, ADDRINT dst, 
        UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(ADDRINT *)get_tag_address(dst) || *(uint128_t *)&thread_ctx->vcpu.avx[src])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src xmm reg: %u - taint %lu \
                dst: %lx - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(uint128_t *)&thread_ctx->vcpu.avx[src],
                dst,  *(uint128_t *)get_tag_address(dst));
#endif
	*(uint128_t *)get_tag_address(dst) |= *(uint128_t *)&thread_ctx->vcpu.avx[src];
#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 2, POST,  M128, dst, XMM, src);
    if(postPropFlag && tainted)
        printLog("Post %s: src xmm: %u - taint %lu \
                dst: %lx - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(uint128_t *)&thread_ctx->vcpu.avx[src],
                dst, *(uint128_t*)get_tag_address(dst));
#endif
}

/* Propagate taint from two 128 bit XMM registers to another XMM 
 * register with form:
 *      t[dst] = t[src1] | t[src2]
 * AVX version: upper 128 bits of dst xmm reg are zeroed
 * @ dst: XMM reg
 * @ src1: XMM reg
 * @ src2: XMM reg
 */

VOID xmm_xmm2xmm_src_union_3op128_zero_upper(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src1, UINT32 src2, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(uint128_t *)&thread_ctx->vcpu.avx[src1] || 
            *(uint128_t *)&thread_ctx->vcpu.avx[src2] || 
            *(uint128_t *)&thread_ctx->vcpu.avx[dst])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src1 xmm: %u - taint %lu \
                src2 xmm: %u taint: %lu dst xmm: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src1, *(uint128_t *)&thread_ctx->vcpu.avx[src1],
                src2, *(uint128_t *)&thread_ctx->vcpu.avx[src2],
                dst, *(uint128_t *)&thread_ctx->vcpu.avx[dst]);
#endif
	*(uint128_t *)&thread_ctx->vcpu.avx[dst] = 
        *(uint128_t *)&thread_ctx->vcpu.avx[src1] | 
        *(uint128_t *)&thread_ctx->vcpu.avx[src2];

    // zero the upper 128 bits of the ymm register
    *(((uint128_t *)&thread_ctx->vcpu.avx[dst]) + 1) = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 3, POST,  XMM, dst, XMM, src1, XMM, src2);
#endif
}

/* Propagate taint from a 128 bit memory location and an XMM register
 * to another XMM register with form:
 *      t[dst] = t[src1] | t[src2]
 * AVX version: upper 128 bits of dst xmm reg are zeroed
 * @ src1: XMM register
 * @ src2: 128-bit memory location
 * @ dst: XMM reg
 */

VOID xmm_m2xmm_src_union_3op128_zero_upper(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src1, ADDRINT src2, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(uint128_t *)&thread_ctx->vcpu.avx[src1] || 
            *(uint128_t *)get_tag_address(src2) || 
            *(uint128_t *)&thread_ctx->vcpu.avx[dst])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src1 xmm: %u taint: %lu src2: %lx - taint %lu \
                dst xmm: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src1, *(uint128_t *)&thread_ctx->vcpu.avx[src1],
                src2, *(uint128_t *)get_tag_address(src2),
                dst, *(uint128_t *)&thread_ctx->vcpu.avx[dst]);
#endif
	*(uint128_t *)&thread_ctx->vcpu.avx[dst] = 
        *(uint128_t *)&thread_ctx->vcpu.avx[src1] | 
        *(uint128_t *)get_tag_address(src2);
    
    // zero the upper 128 bits of the ymm register
    *(((uint128_t *)&thread_ctx->vcpu.avx[dst]) + 1) = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 3, POST,  XMM, dst, XMM, src1, M128, src2);
#endif
}

/* Propagate taint from 64-bit memory location to low qword of 
 * XMM register. The upper qword is not modified.
 *      t[dst_low] = t[src]
 */
VOID m64_2xmm_l_xfer_2op128_l(thread_ctx_t *thread_ctx, UINT32 dst, 
        ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((UINT64 *)&thread_ctx->vcpu.avx[dst]) || *(UINT64 *)get_tag_address(src))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint %lu \
                dst xmm: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(UINT64 *)get_tag_address(src),
                dst, *((UINT64 *)&thread_ctx->vcpu.avx[dst]));
#endif
	*((UINT64 *)&thread_ctx->vcpu.avx[dst]) = 
        *(UINT64 *)get_tag_address(src);
#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 2, POST,  XMM, dst, M64, src);
#endif
}

/* Propagate taint from 64-bit memory location to high qword of 
 * XMM register. The upper qword is not modified.
 *      t[dst_high] = t[src]
 */
VOID m64_2xmm_h_xfer_2op128_h(thread_ctx_t *thread_ctx, UINT32 dst, 
        ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + 1) || 
            *(UINT64 *)get_tag_address(src))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint %lu \
                dst xmm: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(UINT64 *)get_tag_address(src),
                dst, *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + 1));
#endif
	*(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + 1) = 
        *(UINT64 *)get_tag_address(src);
#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 2, POST,  XMM, dst, M64, src);
#endif
}

/* Propagate taint from 64-bit memory location to the low quadword of dst 
 * XMM reg (xmm2) and high qword of src xmm reg (xmm1) to high qword of dst (xmm2). 
 *      t[dst_low] = t[src2]
 *      t[dst_high] = t[src1_high]
 *  @dst: XMM register
 *  @src1: XMM register
 *  @src2: 64-bit memory location
 *
 *  MOVLPD
 */
VOID m64_xmm_h2xmm_xfer_2op128_l(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src1, ADDRINT src2, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(uint128_t *)&thread_ctx->vcpu.avx[dst] || 
            *(((UINT64 *)&thread_ctx->vcpu.avx[src1]) + 1) || 
            *(UINT64 *)get_tag_address(src2))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src1 xmm: %u - taint %lu src2: %lx taint %lx \
                dst xmm: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src1, *(((UINT64 *)&thread_ctx->vcpu.avx[src1]) + 1),
                src2, *(UINT64 *)get_tag_address(src2),
                dst, *(uint128_t *)&thread_ctx->vcpu.avx[dst]);
#endif
	*((UINT64 *)&thread_ctx->vcpu.avx[dst]) = 
        *(UINT64 *)get_tag_address(src2);
    *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + 1) = 
        *(((UINT64 *)&thread_ctx->vcpu.avx[src1]) + 1);
#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 3, POST,  XMM, dst, XMM, src1, M64, src2);
#endif
}

/* Propagate taint from 64-bit memory location to the high quadword of dst 
 * XMM reg (xmm2) and low qword of src xmm reg (xmm1) to low qword of dst (xmm2). 
 *      t[dst_low] = t[src1_low]
 *      t[dst_high] = t[src2]
 *  @dst: XMM register
 *  @src1: XMM register
 *  @src2: 64-bit memory location
 *
 *  MOVLPD
 */
VOID m64_xmm_l2xmm_xfer_2op128_h(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src1, ADDRINT src2, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(uint128_t *)&thread_ctx->vcpu.avx[dst] || 
            *((UINT64 *)&thread_ctx->vcpu.avx[src1]) || 
            *(UINT64 *)get_tag_address(src2))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src1 xmm: %u - taint %lu src2: %lx taint %lx \
                dst xmm: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src1, *((UINT64 *)&thread_ctx->vcpu.avx[src1]),
                src2, *(UINT64 *)get_tag_address(src2),
                dst, *(uint128_t *)&thread_ctx->vcpu.avx[dst]);
#endif
	*((UINT64 *)&thread_ctx->vcpu.avx[dst]) = 
        *(UINT64 *)&thread_ctx->vcpu.avx[src1];
    *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + 1) = 
        *(UINT64 *)get_tag_address(src2);
#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 3, POST,  XMM, dst, XMM, src1, M64, src2);
#endif
}

/* Propagate taint the low qword of an XMM register to a 64 bit 
 * memory location. The upper qword is not modified.
 *      t[dst = t[src_low]
 */
VOID xmm_l2m64_xfer_2op128_l(thread_ctx_t *thread_ctx, UINT32 dst, 
        ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*((UINT64 *)&thread_ctx->vcpu.avx[src]) || *(UINT64 *)get_tag_address(dst))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src xmm: %u - taint %lu \
                dst: %lx - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *((UINT64 *)&thread_ctx->vcpu.avx[src]),
                dst, *(UINT64 *)get_tag_address(dst));
#endif
    *(UINT64 *)get_tag_address(dst) = 
    	*((UINT64 *)&thread_ctx->vcpu.avx[src]);
#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 2, POST,  XMM, dst, M64, src);
#endif
}

/* Propagate taint the high qword of an XMM register to a 64 bit 
 * memory location. The upper qword is not modified.
 *      t[dst = t[src_high]
 */
VOID xmm_h2m64_xfer_2op128_h(thread_ctx_t *thread_ctx, UINT32 dst, 
        ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(((UINT64 *)&thread_ctx->vcpu.avx[src]) + 1) || 
            *(UINT64 *)get_tag_address(dst))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src xmm: %u - taint %lu \
                dst: %lx - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(((UINT64 *)&thread_ctx->vcpu.avx[src]) + 1),
                dst, *(UINT64 *)get_tag_address(dst));
#endif
    *(UINT64 *)get_tag_address(dst) = 
    	*(((UINT64 *)&thread_ctx->vcpu.avx[src]) + 1);
#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 2, POST,  XMM, dst, M64, src);
#endif
}


/* Propagate taint from a 32-bit gpr to the lower 32-bits of an XMM 
 * register with form:
 *      t[dst_low] = t[src]
 *  Zero up to 128 bits of the dst XMM registers
 * @ src: 32-bit register
 * @ dst: XMM reg
 */

VOID r2xmm_xfer_2op32_zx128(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.gpr[src] || thread_ctx->vcpu.avx[dst][0])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src gpr: %u - taint %lu \
                dst xmm: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, thread_ctx->vcpu.gpr[src],
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
    //zero 128 bits
    thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // propagate taint to lower 32-bits 
	*((UINT32 *)&thread_ctx->vcpu.avx[dst]) = 
        *((UINT32 *)&thread_ctx->vcpu.gpr[src]);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src gpr: %u - taint %lu \
                dst xmm: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, thread_ctx->vcpu.gpr[src],
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
}

/* Propagate taint from a 32-bit gpr to the lower 32-bits of an XMM 
 * register with form:
 *      t[dst_low] = t[src]
 *  Zero the full 256 bits of the dst XMM registers
 * @ src: 32-bit gpr
 * @ dst: XMM reg
 */

VOID r2xmm_xfer_2op32_zx256(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.gpr[src] || thread_ctx->vcpu.avx[dst][0] ||
            thread_ctx->vcpu.avx[dst][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src gpr: %u - taint %lu \
                dst xmm: %u - taint %lu %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, thread_ctx->vcpu.gpr[src],
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1]);
#endif
    //zero 128 bits
    thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    thread_ctx->vcpu.avx[dst][1] = TAG_ZERO;
    // propagate taint to lower 32-bits 
	*((UINT32 *)&thread_ctx->vcpu.avx[dst]) = 
        *((UINT32 *)&thread_ctx->vcpu.gpr[src]);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src gpr: %u - taint %lu \
                dst xmm: %u - taint %lu %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, thread_ctx->vcpu.gpr[src],
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1]);
#endif
}

/* Propagate taint from the lower 32-bits of an XMM register to 
 * a 32-bit gpr with form:
 *      t[dst_low] = t[src]
 * @ src: XMM register 
 * @ dst: 32-bit gpr
 */

VOID xmm2r_xfer_2op32(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(UINT32 *)&thread_ctx->vcpu.avx[src] || thread_ctx->vcpu.gpr[dst])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src xmm: %u - taint %lu \
                dst gpr: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(UINT32 *)&thread_ctx->vcpu.avx[src],
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
	*((UINT32 *)&thread_ctx->vcpu.gpr[dst]) = 
        *((UINT32 * )&thread_ctx->vcpu.avx[src]);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src gpr: %u - taint %lu \
                dst xmm: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(UINT32 *)&thread_ctx->vcpu.avx[src],
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
}

/* Propagate taint from a 32-bit memory location to the lower 32-bits of an XMM 
 * register with form:
 *      t[dst_low] = t[src]
 *  Zero up to 128 bits of the dst XMM registers
 * @ src: 32-bit memory location
 * @ dst: XMM reg
 */

VOID m2xmm_xfer_2op32_zx128(thread_ctx_t *thread_ctx, UINT32 dst, 
        ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(UINT32 *)get_tag_address(src) || thread_ctx->vcpu.avx[dst][0])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint %lu \
                dst xmm: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(UINT32 *)get_tag_address(src),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
    //zero 128 bits
    thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // propagate taint to lower 32-bits 
	*((UINT32 *)&thread_ctx->vcpu.avx[dst]) = 
        *(UINT32 *)get_tag_address(src);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src: %lx - taint %lu \
                dst xmm: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(UINT32 *)get_tag_address(src),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
}

/* Propagate taint from a 32-bit memory location to the lower 32-bits of an XMM 
 * register with form:
 *      t[dst_low] = t[src]
 *  Zero the full 256 bits of the dst XMM registers
 * @ src: 32-bit memory location
 * @ dst: XMM reg
 */

VOID m2xmm_xfer_2op32_zx256(thread_ctx_t *thread_ctx, UINT32 dst, 
        ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(UINT32 *)get_tag_address(src) || thread_ctx->vcpu.avx[dst][0] ||
            thread_ctx->vcpu.avx[dst][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint %lu \
                dst xmm: %u - taint %lu %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(UINT32 *)get_tag_address(src),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1]);
#endif
    //zero 128 bits
    thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    thread_ctx->vcpu.avx[dst][1] = TAG_ZERO;
    // propagate taint to lower 32-bits 
	*((UINT32 *)&thread_ctx->vcpu.avx[dst]) = 
        *(UINT32 *)get_tag_address(src);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src: %lx - taint %lu \
                dst xmm: %u - taint %lu %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(UINT32 *)get_tag_address(src),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1]);
#endif
}

/* Propagate taint from the lower 32-bits of an XMM register to 
 * a 32-bit memory location with form:
 *      t[dst_low] = t[src]
 * @ src: XMM register 
 * @ dst: 32-bit memory location
 */

VOID xmm2m_xfer_2op32(thread_ctx_t *thread_ctx, ADDRINT dst, 
        UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(UINT32 *)&thread_ctx->vcpu.avx[src] || *(UINT32 *)get_tag_address(dst))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src xmm: %u - taint %lu \
                dst: %lx - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(UINT32 *)&thread_ctx->vcpu.avx[src],
                dst, *(UINT32 *)get_tag_address(dst));
#endif
	*(UINT32 *)get_tag_address(dst) = 
        *((UINT32 * )&thread_ctx->vcpu.avx[src]);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src gpr: %u - taint %lu \
                dst: %lx - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(UINT32 *)&thread_ctx->vcpu.avx[src],
                dst, *(UINT32 *)get_tag_address(dst));
#endif
}

/* Propagate taint from a 64-bit gpr to the lower 64-bits of an XMM 
 * register with form:
 *      t[dst_low] = t[src]
 *  Zero up to 128 bits of the dst XMM registers
 * @ src: 64-bit register
 * @ dst: XMM reg
 */

VOID r2xmm_xfer_2op64_zx128(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.gpr[src] || thread_ctx->vcpu.avx[dst][0])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src gpr: %u - taint %lu \
                dst xmm: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, thread_ctx->vcpu.gpr[src],
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
    //zero 128 bits
    thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // propagate taint to lower 32-bits 
	*((UINT64 *)&thread_ctx->vcpu.avx[dst]) = 
        *((UINT64 *)&thread_ctx->vcpu.gpr[src]);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src gpr: %u - taint %lu \
                dst xmm: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, thread_ctx->vcpu.gpr[src],
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
}

/* Propagate taint from a 64-bit gpr to the lower 64-bits of an XMM 
 * register with form:
 *      t[dst_low] = t[src]
 *  Zero the full 256 bits of the dst XMM registers
 * @ src: 64-bit gpr
 * @ dst: XMM reg
 */

VOID r2xmm_xfer_2op64_zx256(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.gpr[src] || thread_ctx->vcpu.avx[dst][0] ||
            thread_ctx->vcpu.avx[dst][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src gpr: %u - taint %lu \
                dst xmm: %u - taint %lu %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, thread_ctx->vcpu.gpr[src],
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1]);
#endif
    //zero 128 bits
    thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    thread_ctx->vcpu.avx[dst][1] = TAG_ZERO;
    // propagate taint to lower 32-bits 
	*((UINT64 *)&thread_ctx->vcpu.avx[dst]) = 
        *((UINT64 *)&thread_ctx->vcpu.gpr[src]);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src gpr: %u - taint %lu \
                dst xmm: %u - taint %lu %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, thread_ctx->vcpu.gpr[src],
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1]);
#endif
}

/* Propagate taint from the lower 64-bits of an XMM register to 
 * a 6-bit gpr with form:
 *      t[dst_low] = t[src]
 * @ src: XMM register 
 * @ dst: 64-bit gpr
 */

VOID xmm2r_xfer_2op64(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(UINT64 *)&thread_ctx->vcpu.avx[src] || thread_ctx->vcpu.gpr[dst])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src xmm: %u - taint %lu \
                dst gpr: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(UINT64 *)&thread_ctx->vcpu.avx[src],
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
	*((UINT64 *)&thread_ctx->vcpu.gpr[dst]) = 
        *((UINT64 * )&thread_ctx->vcpu.avx[src]);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src gpr: %u - taint %lu \
                dst xmm: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(UINT64 *)&thread_ctx->vcpu.avx[src],
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
}

/* Propagate taint from a 64-bit memory location to the lower 64-bits of an XMM 
 * register with form:
 *      t[dst_low] = t[src]
 *  Zero up to 128 bits of the dst XMM registers
 * @ src: 64-bit memory location
 * @ dst: XMM reg
 */

VOID m2xmm_xfer_2op64_zx128(thread_ctx_t *thread_ctx, UINT32 dst, 
        ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(UINT64 *)get_tag_address(src) || thread_ctx->vcpu.avx[dst][0])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint %lu \
                dst xmm: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(UINT64 *)get_tag_address(src),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
    //zero 128 bits
    thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // propagate taint to lower 64-bits 
	*((UINT64 *)&thread_ctx->vcpu.avx[dst]) = 
        *(UINT64 *)get_tag_address(src);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src: %lx - taint %lu \
                dst xmm: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(UINT64 *)get_tag_address(src),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
}

/* Propagate taint from a 64-bit memory location to the lower 64-bits of an XMM 
 * register with form:
 *      t[dst_low] = t[src]
 *  Zero the full 256 bits of the dst XMM registers
 * @ src: 64-bit memory location
 * @ dst: XMM reg
 */

VOID m2xmm_xfer_2op64_zx256(thread_ctx_t *thread_ctx, UINT32 dst, 
        ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(UINT64 *)get_tag_address(src) || thread_ctx->vcpu.avx[dst][0] ||
            thread_ctx->vcpu.avx[dst][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src: %lx - taint %lu \
                dst xmm: %u - taint %lu %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(UINT64 *)get_tag_address(src),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1]);
#endif
    //zero 128 bits
    thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    thread_ctx->vcpu.avx[dst][1] = TAG_ZERO;
    // propagate taint to lower 64-bits 
	*((UINT64 *)&thread_ctx->vcpu.avx[dst]) = 
        *(UINT64 *)get_tag_address(src);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src: %lx - taint %lu \
                dst xmm: %u - taint %lu %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(UINT64 *)get_tag_address(src),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1]);
#endif
}

/* Propagate taint from the lower 64-bits of an XMM register to 
 * a 64-bit memory location with form:
 *      t[dst_low] = t[src]
 * @ src: XMM register 
 * @ dst: 64-bit memory location
 */

VOID xmm2m_xfer_2op64(thread_ctx_t *thread_ctx, ADDRINT dst, 
        UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(UINT64 *)&thread_ctx->vcpu.avx[src] || *(UINT64 *)get_tag_address(dst))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src xmm: %u - taint %lu \
                dst: %lx - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(UINT64 *)&thread_ctx->vcpu.avx[src],
                dst, *(UINT64 *)get_tag_address(dst));
#endif
	*(UINT64 *)get_tag_address(dst) = 
        *((UINT64 *)&thread_ctx->vcpu.avx[src]);
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src gpr: %u - taint %lu \
                dst: %lx - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(UINT64 *)&thread_ctx->vcpu.avx[src],
                dst, *(UINT64 *)get_tag_address(dst));
#endif
}

/* Propagate taint from an XMM register to the lower word of a 32/64-bit gpr. 
 * The taint for the low 16 bits of the dst is the union of all corresponding 
 * source taint bytes.
 *      t[dst_[0:7]] = t[src[0:7]] | ... | t[src[24:31]]
 *      t[dst_[8:15]] = t[src[32:39] | ... | t[src[120:127]]
 *  The upper bits are zeroed
 * @ src: XMM register 
 * @ dst: gpr register
 */

VOID xmm2r_xfer_op16_zero_upper(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(UINT64 *)&thread_ctx->vcpu.avx[src] || thread_ctx->vcpu.gpr[dst])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src xmm: %u - taint %lx "
                "dst gpr: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, thread_ctx->vcpu.avx[src],
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
    // compute first and second dst taint bytes
    UINT8 tmp_tag_low = 0, tmp_tag_high = 0, i;
    for(i = 0; i < 8; i++)
        tmp_tag_low |= *(((UINT8 *)&thread_ctx->vcpu.avx[src]) + i);
    
    for(i = 8; i < 16; i++)
        tmp_tag_high |= *(((UINT8 *)&thread_ctx->vcpu.avx[src]) + i);
	
    *(UINT8 *)&thread_ctx->vcpu.gpr[dst] = tmp_tag_low;
    *(((UINT8 *)&thread_ctx->vcpu.gpr[dst]) + 1) = tmp_tag_high;

    // Zero upper 48 bytes
	*(((UINT16 *)&thread_ctx->vcpu.gpr[dst]) + 1) = TAG_ZERO;
	*(((UINT32 *)&thread_ctx->vcpu.gpr[dst]) + 1) = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src xmm %u taint %lx "
                "dst gpr: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(UINT64 *)&thread_ctx->vcpu.avx[src],
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
}

/* Shift left taint of an XMM register to the left by count bytes.
 *      t[dst] = t[dst << count]
 *  The upper bits are unmodified
 * @ dst: XMM register 
 * @ count: 8-bit immediate
 */

VOID shiftl_xmm_imm_bytes_2op128(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(uint128_t *)&thread_ctx->vcpu.avx[dst])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst]);
#endif
    // Zero the dst if count > 15
    if(count > 15)
        *(uint128_t *)&thread_ctx->vcpu.avx[dst] = TAG_ZERO;
    else
        *(uint128_t *)&thread_ctx->vcpu.avx[dst] = 
            *(uint128_t *)&thread_ctx->vcpu.avx[dst] << (BIT2BYTE(count));

#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst]);
#endif
}

/* Shift right taint of an XMM register to the left by count bytes.
 *      t[dst] = t[dst >> count]
 *  The upper bits are unmodified
 * @ dst: XMM register 
 * @ count: 8-bit immediate
 */

VOID shiftr_xmm_imm_bytes_2op128(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(uint128_t *)&thread_ctx->vcpu.avx[dst])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst]);
#endif
    // Zero the dst if count > 15
    if(count > 15)
        *(uint128_t *)&thread_ctx->vcpu.avx[dst] = TAG_ZERO;
    else
        *(uint128_t *)&thread_ctx->vcpu.avx[dst] = 
            *(uint128_t *)&thread_ctx->vcpu.avx[dst] >> (BIT2BYTE(count));

#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst]);
#endif
}

/* Shift taint left of an XMM register to the left by count bytes.
 *      t[dst] = t[src] << (count * 8)
 *  The upper bits are zeroed
 * @ dst: XMM register 
 * @ src: XMM register
 * @ count: 8-bit immediate
 */

VOID shiftl_pdq_xmm_imm_bytes_3op128_zero_upper(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src, UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(uint128_t *)&thread_ctx->vcpu.avx[dst] || 
            *(uint128_t *)&thread_ctx->vcpu.avx[src])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm: %u - taint %lx src xmm: %u - taint: 0x%lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(uint128_t *)&thread_ctx->vcpu.avx[dst],
                src, *(uint128_t *)&thread_ctx->vcpu.avx[src]);
#endif
    // Zero the dst if count > 15
    if(count > 15)
        *(uint128_t *)&thread_ctx->vcpu.avx[dst] = TAG_ZERO;
    else
        *(uint128_t *)&thread_ctx->vcpu.avx[dst] = 
            *(uint128_t *)&thread_ctx->vcpu.avx[src] << (BIT2BYTE(count));

    // Zero upper bits
    thread_ctx->vcpu.avx[dst][1] = TAG_ZERO; 
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm: %u - taint %lx src xmm: %u taint: %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(uint128_t *)&thread_ctx->vcpu.avx[dst],
                src, *(uint128_t *)&thread_ctx->vcpu.avx[src]);
#endif
}

/* Shift taint right of an XMM register to the left by count bytes.
 *      t[dst] = t[src] >> (count * 8)
 *  The upper bits are zeroed
 * @ dst: XMM register 
 * @ src: XMM register
 * @ count: 8-bit immediate
 */

VOID shiftr_pdq_xmm_imm_bytes_3op128_zero_upper(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(uint128_t *)&thread_ctx->vcpu.avx[dst] || 
            *(uint128_t *)&thread_ctx->vcpu.avx[src])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm: %u - taint %lx src xmm: %u - taint: 0x%lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(uint128_t *)&thread_ctx->vcpu.avx[dst],
                src, *(uint128_t *)&thread_ctx->vcpu.avx[src]);
#endif
    // Zero the dst if count > 15
    if(count > 15)
        *(uint128_t *)&thread_ctx->vcpu.avx[dst] = TAG_ZERO;
    else
        *(uint128_t *)&thread_ctx->vcpu.avx[dst] = 
            *(uint128_t *)&thread_ctx->vcpu.avx[src] >> (BIT2BYTE(count));

    // Zero upper bits
    thread_ctx->vcpu.avx[dst][1] = TAG_ZERO; 
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm: %u - taint %lx src xmm: %u taint: %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, *(uint128_t *)&thread_ctx->vcpu.avx[dst],
                src, *(uint128_t *)&thread_ctx->vcpu.avx[src]);
#endif
}

/* 
 * Shifts each packed word in dst to left/right count bits. 
 * If count > 15, zero dst. If the bitshift results in byte taint
 * tags overlapping byte-boundaries, we must take the union of the 
 * two byte taint tags. 
 *      if count % 8 == 0: // whole byte shift
 *          t[dst[0:15]] = t[dst[0:15]] <</>> (count/8) * 8)
 *          ...
 *      else // overlapping byte taint tags
 *          t[dst[0:15]] = 
 *              t[dst[0:15]] <</>> (count/8) | t[dst] <</>> ((count/8 + 1) * 8)
 *          ...
 *  The upper bits are unmodified
 * @ dst: XMM register 
 * @ count: 8-bit immediate
 * @ shift_is_left: Bool indicating if shift is to left. If false,
 *      shift is to right
 *
 */
VOID shiftl_pw_xmm_imm_bits_2op128(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
    // Zero the dst if count > 15
    if(count > 15)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits
    else
    {
        uint128_t tmp_tag = thread_ctx->vcpu.avx[dst][0];
        
        // whole byte shift
        for(int i = 0; i < XMM_BITS/WORD_BITS; i++)
            *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT16 *)&tmp_tag) + i) << BYTE_ALIGN(count);
        // overlapping byte tags
        if(count % 8)
            for(int i = 0; i < XMM_BITS/WORD_BITS; i++)
                *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) |= 
                    *(((UINT16 *)&tmp_tag) + i) << (BYTE_ALIGN(count) + BYTE_BITS);
    }
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
}

/* 
 * Shifts each packed word in dst to left/right count bits. 
 * If count > 15, zero dst. If the bitshift results in byte taint
 * tags overlapping byte-boundaries, we must take the union of the 
 * two byte taint tags. 
 *      if count % 8 == 0: // whole byte shift
 *          t[dst[0:15]] = t[dst[0:15]] <</>> (count/8)
 *          ...
 *      else // overlapping byte taint tags
 *          t[dst[0:15]] = 
 *              t[dst[0:15]] <</>> (count/8) | t[dst] <</>> (count/8 + 1)
 *          ...
 * The upper bits are unmodified
 * @ dst: XMM register 
 * @ count_reg: XMM register containing the value of count 
 *      (PIN REG not vcpu index)
 * @ pin_ctx: pointer to pin CONTEXT - needed to extract count from count_reg
 * @ shift_is_left: Bool indicating if shift is to left. If false,
 *      shift is to right
 */
VOID shiftl_pw_xmm_xmm_bits_2op128(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 count_reg, CONTEXT *pin_ctx, 
        UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
    //Extract count from XMM count_reg
    UINT size = REG_Size((REG)count_reg);
    UINT8* count_val = new UINT8[size];
    PIN_GetContextRegval(pin_ctx, (REG)count_reg, count_val);
    UINT32 count = *(UINT32 *)count_val;
    printLog("value of extracted count: %u\n", count);
    
    // Zero the dst if count > 15
    if(count > 15)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits
    else
    {
        uint128_t tmp_tag = thread_ctx->vcpu.avx[dst][0];
        
        // whole byte shift
        for(int i = 0; i < XMM_BITS/WORD_BITS; i++)
            *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT16 *)&tmp_tag) + i) << BYTE_ALIGN(count);
        // overlapping byte tags
        if(count % 8)
            for(int i = 0; i < XMM_BITS/WORD_BITS; i++)
                *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) |= 
                    *(((UINT16 *)&tmp_tag) + i) << (BYTE_ALIGN(count) + BYTE_BITS);
    }
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
}

/* 
 * Shifts each packed word in dst to left/right count bits. 
 * If count > 15, zero dst. If the bitshift results in byte taint
 * tags overlapping byte-boundaries, we must take the union of the 
 * two byte taint tags. 
 *      if count % 8 == 0: // whole byte shift
 *          t[dst[0:15]] = t[dst[0:15]] <</>> (count/8)
 *          ...
 *      else // overlapping byte taint tags
 *          t[dst[0:15]] = 
 *              t[dst[0:15]] <</>> (count/8) | t[dst] <</>> (count/8 + 1)
 *          ...
 * The upper bits are unmodified
 * @ dst: XMM register 
 * @ count_addr: 128-bit memory location
 * @ shift_is_left: Bool indicating if shift is to left. If false,
 *      shift is to right
 */
VOID shiftl_pw_xmm_m_bits_2op128(thread_ctx_t *thread_ctx, 
        UINT32 dst, ADDRINT count_addr, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
    // Extract count from memory
    UINT32 count = *(UINT32 *)count_addr;
    
    // Zero the dst if count > 15
    if(count > 15)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits
    else
    {
        uint128_t tmp_tag = thread_ctx->vcpu.avx[dst][0];
        
        // whole byte shift
        for(int i = 0; i < XMM_BITS/WORD_BITS; i++)
            *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT16 *)&tmp_tag) + i) << BYTE_ALIGN(count);
        // overlapping byte tags
        if(count % 8)
            for(int i = 0; i < XMM_BITS/WORD_BITS; i++)
                *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) |= 
                    *(((UINT16 *)&tmp_tag) + i) << (BYTE_ALIGN(count) + BYTE_BITS);
    }
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
}

/* 
 * Shifts each packed word in dst to left/right count bits. 
 * If count > 15, zero dst. If the bitshift results in byte taint
 * tags overlapping byte-boundaries, we must take the union of the 
 * two byte taint tags. 
 *      if count % 8 == 0: // whole byte shift
 *          t[dst[0:15]] = t[dst[0:15]] <</>> (count/8) * 8)
 *          ...
 *      else // overlapping byte taint tags
 *          t[dst[0:15]] = 
 *              t[dst[0:15]] <</>> (count/8) | t[dst] <</>> ((count/8 + 1) * 8)
 *          ...
 *  The upper bits are unmodified
 * @ dst: XMM register 
 * @ count: 8-bit immediate
 * @ shift_is_left: Bool indicating if shift is to left. If false,
 *      shift is to right
 *
 */
VOID shiftr_pw_xmm_imm_bits_2op128(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
    // Zero the dst if count > 15
    if(count > 15)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits
    else
    {
        uint128_t tmp_tag = thread_ctx->vcpu.avx[dst][0];
        
        // whole byte shift
        for(int i = 0; i < XMM_BITS/WORD_BITS; i++)
            *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT16 *)&tmp_tag) + i) >> BYTE_ALIGN(count);
        // overlapping byte tags
        if(count % 8)
            for(int i = 0; i < XMM_BITS/WORD_BITS; i++)
                *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) |= 
                    *(((UINT16 *)&tmp_tag) + i) >> (BYTE_ALIGN(count) + BYTE_BITS);
    }
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
}

/* 
 * Shifts each packed word in dst to left/right count bits. 
 * If count > 15, zero dst. If the bitshift results in byte taint
 * tags overlapping byte-boundaries, we must take the union of the 
 * two byte taint tags. 
 *      if count % 8 == 0: // whole byte shift
 *          t[dst[0:15]] = t[dst[0:15]] <</>> (count/8)
 *          ...
 *      else // overlapping byte taint tags
 *          t[dst[0:15]] = 
 *              t[dst[0:15]] <</>> (count/8) | t[dst] <</>> (count/8 + 1)
 *          ...
 * The upper bits are unmodified
 * @ dst: XMM register 
 * @ count_reg: XMM register containing the value of count 
 *      (PIN REG not vcpu index)
 * @ pin_ctx: pointer to pin CONTEXT - needed to extract count from count_reg
 * @ shift_is_left: Bool indicating if shift is to left. If false,
 *      shift is to right
 */
VOID shiftr_pw_xmm_xmm_bits_2op128(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 count_reg, CONTEXT *pin_ctx, 
        UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
    //Extract count from XMM count_reg
    UINT size = REG_Size((REG)count_reg);
    UINT8* count_val = new UINT8[size];
    PIN_GetContextRegval(pin_ctx, (REG)count_reg, count_val);
    UINT32 count = *(UINT32 *)count_val;
    printLog("value of extracted count: %u\n", count);
    
    // Zero the dst if count > 15
    if(count > 15)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits
    else
    {
        uint128_t tmp_tag = thread_ctx->vcpu.avx[dst][0];
        
        // whole byte shift
        for(int i = 0; i < XMM_BITS/WORD_BITS; i++)
            *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT16 *)&tmp_tag) + i) >> BYTE_ALIGN(count);
        // overlapping byte tags
        if(count % 8)
            for(int i = 0; i < XMM_BITS/WORD_BITS; i++)
                *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) |= 
                    *(((UINT16 *)&tmp_tag) + i) >> (BYTE_ALIGN(count) + BYTE_BITS);
    }
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
}

/* 
 * Shifts each packed word in dst to left/right count bits. 
 * If count > 15, zero dst. If the bitshift results in byte taint
 * tags overlapping byte-boundaries, we must take the union of the 
 * two byte taint tags. 
 *      if count % 8 == 0: // whole byte shift
 *          t[dst[0:15]] = t[dst[0:15]] <</>> (count/8)
 *          ...
 *      else // overlapping byte taint tags
 *          t[dst[0:15]] = 
 *              t[dst[0:15]] <</>> (count/8) | t[dst] <</>> (count/8 + 1)
 *          ...
 * The upper bits are unmodified
 * @ dst: XMM register 
 * @ count_addr: 128-bit memory location
 * @ shift_is_left: Bool indicating if shift is to left. If false,
 *      shift is to right
 */
VOID shiftr_pw_xmm_m_bits_2op128(thread_ctx_t *thread_ctx, 
        UINT32 dst, ADDRINT count_addr, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
    // Extract count from memory
    UINT32 count = *(UINT32 *)count_addr;
    
    // Zero the dst if count > 15
    if(count > 15)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits
    else
    {
        uint128_t tmp_tag = thread_ctx->vcpu.avx[dst][0];
        
        // whole byte shift
        for(int i = 0; i < XMM_BITS/WORD_BITS; i++)
            *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT16 *)&tmp_tag) + i) >> BYTE_ALIGN(count);
        // overlapping byte tags
        if(count % 8)
            for(int i = 0; i < XMM_BITS/WORD_BITS; i++)
                *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) |= 
                    *(((UINT16 *)&tmp_tag) + i) >> (BYTE_ALIGN(count) + BYTE_BITS);
    }
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
}


/* 
 * Shifts each packed dword in dst to left/right count bits. 
 * If count > 31, zero dst. If the bitshift results in byte taint
 * tags overlapping byte-boundaries, we must take the union of the 
 * two byte taint tags. 
 *      if count % 8 == 0: // whole byte shift
 *          t[dst[0:31]] = t[dst[0:31]] <</>> (count/8)
 *          ...
 *      else // overlapping byte taint tags
 *          t[dst[0:31]] = 
 *              t[dst[0:31]] <</>> 
 *                  (count/8) | t[dst[0:31]] <</>> (count/8 + 1)
 *          ...
 *  The upper bits are unmodified
 * @ dst: XMM register 
 * @ count: 8-bit immediate
 * @ shift_is_left: Bool indicating if shift is to left. If false,
 *      shift is to right
 */
VOID shiftl_pd_xmm_imm_bits_2op128(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif 
    // Zero the dst if count > 31
    if(count > 31)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
    {
        uint128_t tmp_tag = thread_ctx->vcpu.avx[dst][0];
        for(int i = 0; i < XMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT32 *)&tmp_tag) + i) << BYTE_ALIGN(count);
    }
// Else shift each word by count bits, overlapping byte tags 
    else
    {
        uint128_t tmp_tag = thread_ctx->vcpu.avx[dst][0];
        for(int i = 0; i < XMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT32 *)&tmp_tag) + i) << BYTE_ALIGN(count)) |
                (*(((UINT32 *)&tmp_tag) + i) << (BYTE_ALIGN(count) + BYTE_BITS));
    }
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
}

/* 
 * Shifts each packed dword in dst to left/right count bits. 
 * If count > 31, zero dst. If the bitshift results in byte taint
 * tags overlapping byte-boundaries, we must take the union of the 
 * two byte taint tags. 
 *      if count % 8 == 0: // whole byte shift
 *          t[dst[0:31]] = t[dst[0:31]] <</>> (count/8)
 *          ...
 *      else // overlapping byte taint tags
 *          t[dst[0:31]] = 
 *              t[dst[0:31]] <</>> 
 *                  (count/8) | t[dst[0:31]] <</>> (count/8 + 1)
 *          ...
 *  The upper bits are unmodified
 * @ dst: XMM register 
 * @ count_reg: XMM register containing the value of count 
 *      (PIN REG not vcpu index)
 * @ pin_ctx: pointer to pin CONTEXT - needed to extract count from count_reg
 * @ shift_is_left: Bool indicating if shift is to left. If false,
 *      shift is to right
 */
VOID shiftl_pd_xmm_xmm_bits_2op128(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 count_reg, CONTEXT *pin_ctx, 
        UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
    //Extract count from XMM count_reg
    UINT size = REG_Size((REG)count_reg);
    UINT8* count_val = new UINT8[size];
    PIN_GetContextRegval(pin_ctx, (REG)count_reg, count_val);
    UINT32 count = *(UINT32 *)count_val;
    printLog("value of extracted count: %u\n", count);
    
    // Zero the dst if count > 31
    if(count > 31)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
    {
        uint128_t tmp_tag = thread_ctx->vcpu.avx[dst][0];
        for(int i = 0; i < XMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT32 *)&tmp_tag) + i) << BYTE_ALIGN(count);
    }
    // Else shift each word by count bits, overlapping byte tags 
    else
    {
        uint128_t tmp_tag = thread_ctx->vcpu.avx[dst][0];
        for(int i = 0; i < XMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT32 *)&tmp_tag) + i) << BYTE_ALIGN(count)) |
                (*(((UINT32 *)&tmp_tag) + i) << (BYTE_ALIGN(count) + BYTE_BITS));
    }
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
}

/* 
 * Shifts each packed dword in dst to left/right count bits. 
 * If count > 31, zero dst. If the bitshift results in byte taint
 * tags overlapping byte-boundaries, we must take the union of the 
 * two byte taint tags. 
 *      if count % 8 == 0: // whole byte shift
 *          t[dst[0:31]] = t[dst[0:31]] <</>> (count/8)
 *          ...
 *      else // overlapping byte taint tags
 *          t[dst[0:31]] = 
 *              t[dst[0:31]] <</>> 
 *                  (count/8) | t[dst[0:31]] <</>> (count/8 + 1)
 *          ...
 *  The upper bits are unmodified
 * @ dst: XMM register 
 * @ count_addr: 128-bit memory location
 * @ shift_is_left: Bool indicating if shift is to left. If false,
 *      shift is to right
 */
VOID shiftl_pd_xmm_m_bits_2op128(thread_ctx_t *thread_ctx, 
        UINT32 dst, ADDRINT count_addr, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
    // Extract count from memory
    UINT32 count = *(UINT32 *)count_addr;
    
    // Zero the dst if count > 31
    if(count > 31)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
    {
        uint128_t tmp_tag = thread_ctx->vcpu.avx[dst][0];
        for(int i = 0; i < XMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT32 *)&tmp_tag) + i) << BYTE_ALIGN(count);
    }
    // Else shift each word by count bits, overlapping byte tags 
    else
    {
        uint128_t tmp_tag = thread_ctx->vcpu.avx[dst][0];
        for(int i = 0; i < XMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT32 *)&tmp_tag) + i) << BYTE_ALIGN(count)) |
                (*(((UINT32 *)&tmp_tag) + i) << (BYTE_ALIGN(count) + BYTE_BITS));
    }
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
}

/* 
 * Shifts each packed dword in dst to left/right count bits. 
 * If count > 31, zero dst. If the bitshift results in byte taint
 * tags overlapping byte-boundaries, we must take the union of the 
 * two byte taint tags. 
 *      if count % 8 == 0: // whole byte shift
 *          t[dst[0:31]] = t[dst[0:31]] <</>> (count/8)
 *          ...
 *      else // overlapping byte taint tags
 *          t[dst[0:31]] = 
 *              t[dst[0:31]] <</>> 
 *                  (count/8) | t[dst[0:31]] <</>> (count/8 + 1)
 *          ...
 *  The upper bits are unmodified
 * @ dst: XMM register 
 * @ count: 8-bit immediate
 * @ shift_is_left: Bool indicating if shift is to left. If false,
 *      shift is to right
 */
VOID shiftr_pd_xmm_imm_bits_2op128(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif 
    // Zero the dst if count > 31
    if(count > 31)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
    {
        uint128_t tmp_tag = thread_ctx->vcpu.avx[dst][0];
        for(int i = 0; i < XMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT32 *)&tmp_tag) + i) >> BYTE_ALIGN(count);
    }
    // Else shift each word by count bits, overlapping byte tags 
    else
    {
        uint128_t tmp_tag = thread_ctx->vcpu.avx[dst][0];
        for(int i = 0; i < XMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT32 *)&tmp_tag) + i) >> BYTE_ALIGN(count)) |
                (*(((UINT32 *)&tmp_tag) + i) >> (BYTE_ALIGN(count) + BYTE_BITS));
    }
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
}

/* 
 * Shifts each packed dword in dst to left/right count bits. 
 * If count > 31, zero dst. If the bitshift results in byte taint
 * tags overlapping byte-boundaries, we must take the union of the 
 * two byte taint tags. 
 *      if count % 8 == 0: // whole byte shift
 *          t[dst[0:31]] = t[dst[0:31]] <</>> (count/8)
 *          ...
 *      else // overlapping byte taint tags
 *          t[dst[0:31]] = 
 *              t[dst[0:31]] <</>> 
 *                  (count/8) | t[dst[0:31]] <</>> (count/8 + 1)
 *          ...
 *  The upper bits are unmodified
 * @ dst: XMM register 
 * @ count_reg: XMM register containing the value of count 
 *      (PIN REG not vcpu index)
 * @ pin_ctx: pointer to pin CONTEXT - needed to extract count from count_reg
 * @ shift_is_left: Bool indicating if shift is to left. If false,
 *      shift is to right
 */
VOID shiftr_pd_xmm_xmm_bits_2op128(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 count_reg, CONTEXT *pin_ctx, 
        UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
    //Extract count from XMM count_reg
    UINT size = REG_Size((REG)count_reg);
    UINT8* count_val = new UINT8[size];
    PIN_GetContextRegval(pin_ctx, (REG)count_reg, count_val);
    UINT32 count = *(UINT32 *)count_val;
    printLog("value of extracted count: %u\n", count);
    
    // Zero the dst if count > 31
    if(count > 31)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
    {
        uint128_t tmp_tag = thread_ctx->vcpu.avx[dst][0];
        for(int i = 0; i < XMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT32 *)&tmp_tag) + i) >> BYTE_ALIGN(count);
    }
    // Else shift each word by count bits, overlapping byte tags 
    else
    {
        uint128_t tmp_tag = thread_ctx->vcpu.avx[dst][0];
        for(int i = 0; i < XMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT32 *)&tmp_tag) + i) >> BYTE_ALIGN(count)) |
                (*(((UINT32 *)&tmp_tag) + i) >> (BYTE_ALIGN(count) + BYTE_BITS));
    }
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
}

/* 
 * Shifts each packed dword in dst to left/right count bits. 
 * If count > 31, zero dst. If the bitshift results in byte taint
 * tags overlapping byte-boundaries, we must take the union of the 
 * two byte taint tags. 
 *      if count % 8 == 0: // whole byte shift
 *          t[dst[0:31]] = t[dst[0:31]] <</>> (count/8)
 *          ...
 *      else // overlapping byte taint tags
 *          t[dst[0:31]] = 
 *              t[dst[0:31]] <</>> 
 *                  (count/8) | t[dst[0:31]] <</>> (count/8 + 1)
 *          ...
 *  The upper bits are unmodified
 * @ dst: XMM register 
 * @ count_addr: 128-bit memory location
 * @ shift_is_left: Bool indicating if shift is to left. If false,
 *      shift is to right
 */
VOID shiftr_pd_xmm_m_bits_2op128(thread_ctx_t *thread_ctx, 
        UINT32 dst, ADDRINT count_addr, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
    // Extract count from memory
    UINT32 count = *(UINT32 *)count_addr;
    
    // Zero the dst if count > 31
    if(count > 31)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
    {
        uint128_t tmp_tag = thread_ctx->vcpu.avx[dst][0];
        for(int i = 0; i < XMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT32 *)&tmp_tag) + i) >> BYTE_ALIGN(count);
    }
    // Else shift each word by count bits, overlapping byte tags 
    else
    {
        uint128_t tmp_tag = thread_ctx->vcpu.avx[dst][0];
        for(int i = 0; i < XMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT32 *)&tmp_tag) + i) >> BYTE_ALIGN(count)) |
                (*(((UINT32 *)&tmp_tag) + i) >> (BYTE_ALIGN(count) + BYTE_BITS));
    }
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
}



/* 
 * Shifts each packed qword in dst to left/right count bits. 
 * If count > 63, zero dst. If the bitshift results in byte taint
 * tags overlapping byte-boundaries, we must take the union of the 
 * two byte taint tags. 
 *      if count % 8 == 0: // whole byte shift
 *          t[dst[0:63]] = t[dst[0:63]] <</>> (count/8)
 *          ...
 *      else // overlapping byte taint tags
 *          t[dst[0:63]] = 
 *              t[dst[0:63]] <</>> 
 *                  (count/8) | t[dst[0:63]] <</>> (count/8 + 1)
 *          ...
 *  The upper bits are unmodified
 * @ dst: XMM register 
 * @ count: 8-bit immediate
 */
VOID shiftl_pq_xmm_imm_bits_2op128(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif 
    // Zero the dst if count > 63
    if(count > 63)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
    {
        uint128_t tmp_tag = thread_ctx->vcpu.avx[dst][0];
        for(int i = 0; i < XMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT64 *)&tmp_tag) + i) << BYTE_ALIGN(count);
    }
    // Else shift each word by count bits, overlapping byte tags 
    else
    {
        uint128_t tmp_tag = thread_ctx->vcpu.avx[dst][0];
        for(int i = 0; i < XMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT64 *)&tmp_tag) + i) << BYTE_ALIGN(count)) |
                (*(((UINT64 *)&tmp_tag) + i) << (BYTE_ALIGN(count) + BYTE_BITS));
    }
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
}

/* 
 * Shifts each packed qword in dst to left/right count bits. 
 * If count > 63, zero dst. If the bitshift results in byte taint
 * tags overlapping byte-boundaries, we must take the union of the 
 * two byte taint tags. 
 *      if count % 8 == 0: // whole byte shift
 *          t[dst[0:63]] = t[dst[0:63]] <</>> (count/8)
 *          ...
 *      else // overlapping byte taint tags
 *          t[dst[0:63]] = 
 *              t[dst[0:63]] <</>> 
 *                  (count/8) | t[dst[0:63]] <</>> (count/8 + 1)
 *          ...
 *  The upper bits are unmodified
 * @ dst: XMM register 
 * @ count_reg: XMM register containing the value of count 
 *      (PIN REG not vcpu index)
 * @ pin_ctx: pointer to pin CONTEXT - needed to extract count from count_reg
 */
VOID shiftl_pq_xmm_xmm_bits_2op128(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 count_reg, CONTEXT *pin_ctx, 
        UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
    //Extract count from XMM count_reg
    UINT size = REG_Size((REG)count_reg);
    UINT8* count_val = new UINT8[size];
    PIN_GetContextRegval(pin_ctx, (REG)count_reg, count_val);
    UINT32 count = *(UINT32 *)count_val;
    printLog("value of extracted count: %u\n", count);

    // Zero the dst if count > 63
    if(count > 63)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
    {
        uint128_t tmp_tag = thread_ctx->vcpu.avx[dst][0];
        for(int i = 0; i < XMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT64 *)&tmp_tag) + i) << BYTE_ALIGN(count);
    }
    // Else shift each word by count bits, overlapping byte tags 
    else
    {
        uint128_t tmp_tag = thread_ctx->vcpu.avx[dst][0];
        for(int i = 0; i < XMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT64 *)&tmp_tag) + i) << BYTE_ALIGN(count)) |
                (*(((UINT64 *)&tmp_tag) + i) << (BYTE_ALIGN(count) + BYTE_BITS));
    }
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
}

/* 
 * Shifts each packed qword in dst to left/right count bits. 
 * If count > 63, zero dst. If the bitshift results in byte taint
 * tags overlapping byte-boundaries, we must take the union of the 
 * two byte taint tags. 
 *      if count % 8 == 0: // whole byte shift
 *          t[dst[0:63]] = t[dst[0:63]] <</>> (count/8)
 *          ...
 *      else // overlapping byte taint tags
 *          t[dst[0:63]] = 
 *              t[dst[0:63]] <</>> 
 *                  (count/8) | t[dst[0:63]] <</>> (count/8 + 1)
 *          ...
 *  The upper bits are unmodified
 * @ dst: XMM register 
 * @ count_addr: 128-bit memory location
 */
VOID shiftl_pq_xmm_m_bits_2op128(thread_ctx_t *thread_ctx, 
        UINT32 dst, ADDRINT count_addr, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
    // Extract count from memory
    UINT32 count = *(UINT32 *)count_addr;
    
    // Zero the dst if count > 63
    if(count > 63)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
    {
        uint128_t tmp_tag = thread_ctx->vcpu.avx[dst][0];
        for(int i = 0; i < XMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT64 *)&tmp_tag) + i) << BYTE_ALIGN(count);
    }
    // Else shift each word by count bits, overlapping byte tags 
    else
    {
        uint128_t tmp_tag = thread_ctx->vcpu.avx[dst][0];
        for(int i = 0; i < XMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT64 *)&tmp_tag) + i) << BYTE_ALIGN(count)) |
                (*(((UINT64 *)&tmp_tag) + i) << (BYTE_ALIGN(count) + BYTE_BITS));
    }
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
}

/* 
 * Shifts each packed qword in dst to left/right count bits. 
 * If count > 63, zero dst. If the bitshift results in byte taint
 * tags overlapping byte-boundaries, we must take the union of the 
 * two byte taint tags. 
 *      if count % 8 == 0: // whole byte shift
 *          t[dst[0:63]] = t[dst[0:63]] <</>> (count/8)
 *          ...
 *      else // overlapping byte taint tags
 *          t[dst[0:63]] = 
 *              t[dst[0:63]] <</>> 
 *                  (count/8) | t[dst[0:63]] <</>> (count/8 + 1)
 *          ...
 *  The upper bits are unmodified
 * @ dst: XMM register 
 * @ count: 8-bit immediate
 */
VOID shiftr_pq_xmm_imm_bits_2op128(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif 
    // Zero the dst if count > 63
    if(count > 63)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
    {
        uint128_t tmp_tag = thread_ctx->vcpu.avx[dst][0];
        for(int i = 0; i < XMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT64 *)&tmp_tag) + i) >> BYTE_ALIGN(count);
    }
    // Else shift each word by count bits, overlapping byte tags 
    else
    {
        uint128_t tmp_tag = thread_ctx->vcpu.avx[dst][0];
        for(int i = 0; i < XMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT64 *)&tmp_tag) + i) >> BYTE_ALIGN(count)) |
                (*(((UINT64 *)&tmp_tag) + i) >> (BYTE_ALIGN(count) + BYTE_BITS));
    }
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
}

/* 
 * Shifts each packed qword in dst to left/right count bits. 
 * If count > 63, zero dst. If the bitshift results in byte taint
 * tags overlapping byte-boundaries, we must take the union of the 
 * two byte taint tags. 
 *      if count % 8 == 0: // whole byte shift
 *          t[dst[0:63]] = t[dst[0:63]] <</>> (count/8)
 *          ...
 *      else // overlapping byte taint tags
 *          t[dst[0:63]] = 
 *              t[dst[0:63]] <</>> 
 *                  (count/8) | t[dst[0:63]] <</>> (count/8 + 1)
 *          ...
 *  The upper bits are unmodified
 * @ dst: XMM register 
 * @ count_reg: XMM register containing the value of count 
 *      (PIN REG not vcpu index)
 * @ pin_ctx: pointer to pin CONTEXT - needed to extract count from count_reg
 */
VOID shiftr_pq_xmm_xmm_bits_2op128(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 count_reg, CONTEXT *pin_ctx, 
        UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
    //Extract count from XMM count_reg
    UINT size = REG_Size((REG)count_reg);
    UINT8* count_val = new UINT8[size];
    PIN_GetContextRegval(pin_ctx, (REG)count_reg, count_val);
    UINT32 count = *(UINT32 *)count_val;
    printLog("value of extracted count: %u\n", count);

    // Zero the dst if count > 63
    if(count > 63)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
    {
        uint128_t tmp_tag = thread_ctx->vcpu.avx[dst][0];
        for(int i = 0; i < XMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT64 *)&tmp_tag) + i) >> BYTE_ALIGN(count);
    }
    // Else shift each word by count bits, overlapping byte tags 
    else
    {
        uint128_t tmp_tag = thread_ctx->vcpu.avx[dst][0];
        for(int i = 0; i < XMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT64 *)&tmp_tag) + i) >> BYTE_ALIGN(count)) |
                (*(((UINT64 *)&tmp_tag) + i) >> (BYTE_ALIGN(count) + BYTE_BITS));
    }
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
}

/* 
 * Shifts each packed qword in dst to left/right count bits. 
 * If count > 63, zero dst. If the bitshift results in byte taint
 * tags overlapping byte-boundaries, we must take the union of the 
 * two byte taint tags. 
 *      if count % 8 == 0: // whole byte shift
 *          t[dst[0:63]] = t[dst[0:63]] <</>> (count/8)
 *          ...
 *      else // overlapping byte taint tags
 *          t[dst[0:63]] = 
 *              t[dst[0:63]] <</>> 
 *                  (count/8) | t[dst[0:63]] <</>> (count/8 + 1)
 *          ...
 *  The upper bits are unmodified
 * @ dst: XMM register 
 * @ count_addr: 128-bit memory location
 */
VOID shiftr_pq_xmm_m_bits_2op128(thread_ctx_t *thread_ctx, 
        UINT32 dst, ADDRINT count_addr, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
    // Extract count from memory
    UINT32 count = *(UINT32 *)count_addr;
    
    // Zero the dst if count > 63
    if(count > 63)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
    {
        uint128_t tmp_tag = thread_ctx->vcpu.avx[dst][0];
        for(int i = 0; i < XMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT64 *)&tmp_tag) + i) >> BYTE_ALIGN(count);
    }
    // Else shift each word by count bits, overlapping byte tags 
    else
    {
        uint128_t tmp_tag = thread_ctx->vcpu.avx[dst][0];
        for(int i = 0; i < XMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT64 *)&tmp_tag) + i) >> BYTE_ALIGN(count)) |
                (*(((UINT64 *)&tmp_tag) + i) >> (BYTE_ALIGN(count) + BYTE_BITS));
    }
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0]);
#endif
}


/* Shift taint left of each packed word in an XMM register to the left by 
 * count bits. If count > 15, zero the taint
 *      t[dst[0:15]] = t[dst[0:15]] << count
 *      ...
 *  AVX version: upper bits are zeroed
 * @ dst: XMM register 
 * @ src: XMM register
 * @ count: 8-bit immediate
 */

VOID shiftl_pw_xmm_imm_bits_3op128_zero_upper(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    // Zero the dst if count > 15
    if(count > 15)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < XMM_BITS/WORD_BITS; i++)
            *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < XMM_BITS/WORD_BITS; i++)
            *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count)) |
                (*(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) << 
                    (BYTE_ALIGN(count) + BYTE_BITS));
    
    // Zero upper 128 bits
    thread_ctx->vcpu.avx[dst][1] = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}

/* Shift taint left of each packed word in an XMM register to the left by 
 * count bits. If count > 15, zero the taint
 *      t[dst[0:15]] = t[dst[0:15]] << count
 *      ...
 *  AVX version: upper bits are zeroed
 * @ dst: XMM register 
 * @ src: XMM register
 * @ count_reg: XMM register containing the value of count 
 *      (PIN REG not vcpu index)
 * @ pin_ctx: pointer to pin CONTEXT - needed to extract count from count_reg
 */

VOID shiftl_pw_xmm_xmm_bits_3op128_zero_upper(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, UINT32 count_reg, 
        CONTEXT *pin_ctx, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    //Extract count from XMM count_reg
    UINT size = REG_Size((REG)count_reg);
    UINT8* count_val = new UINT8[size];
    PIN_GetContextRegval(pin_ctx, (REG)count_reg, count_val);
    UINT32 count = *(UINT32 *)count_val;
    printLog("value of extracted count: %u\n", count);
    // Zero the dst if count > 15
    if(count > 15)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < XMM_BITS/WORD_BITS; i++)
            *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < XMM_BITS/WORD_BITS; i++)
            *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count)) |
                (*(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) << 
                    (BYTE_ALIGN(count) + BYTE_BITS));
    
    // Zero upper 128 bits
    thread_ctx->vcpu.avx[dst][1] = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}

/* Shift taint left of each packed word in an XMM register to the left by 
 * count bits. If count > 15, zero the taint
 *      t[dst[0:15]] = t[dst[0:15]] << count
 *      ...
 *  AVX version: upper bits are zeroed
 * @ dst: XMM register 
 * @ src: XMM register
 * @ count: 128-bit memory location
 */

VOID shiftl_pw_xmm_m_bits_3op128_zero_upper(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, ADDRINT count_addr, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    //Extract count from memory
    UINT32 count = *(UINT32 *)count_addr;
    // Zero the dst if count > 15
    if(count > 15)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < XMM_BITS/WORD_BITS; i++)
            *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < XMM_BITS/WORD_BITS; i++)
            *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count)) |
                (*(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) << 
                    (BYTE_ALIGN(count) + BYTE_BITS));
    
    // Zero upper 128 bits
    thread_ctx->vcpu.avx[dst][1] = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}

/* Shift taint right of each packed word in an XMM register to the left by 
 * count bits. If count > 15, zero the taint
 *      t[dst[0:15]] = t[dst[0:15]] >> count
 *      ...
 *  AVX version: upper bits are zeroed
 * @ dst: XMM register 
 * @ src: XMM register
 * @ count: 8-bit immediate
 */

VOID shiftr_pw_xmm_imm_bits_3op128_zero_upper(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    // Zero the dst if count > 15
    if(count > 15)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < XMM_BITS/WORD_BITS; i++)
            *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < XMM_BITS/WORD_BITS; i++)
            *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count)) |
                (*(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) >> 
                    (BYTE_ALIGN(count) + BYTE_BITS));
    
    // Zero upper 128 bits
    thread_ctx->vcpu.avx[dst][1] = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}

/* Shift taint right of each packed word in an XMM register to the left by 
 * count bits. If count > 15, zero the taint
 *      t[dst[0:15]] = t[dst[0:15]] >> count
 *      ...
 *  AVX version: upper bits are zeroed
 * @ dst: XMM register 
 * @ src: XMM register
 * @ count_reg: XMM register containing the value of count 
 *      (PIN REG not vcpu index)
 * @ pin_ctx: pointer to pin CONTEXT - needed to extract count from count_reg
 */

VOID shiftr_pw_xmm_xmm_bits_3op128_zero_upper(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, UINT32 count_reg, 
        CONTEXT *pin_ctx, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    //Extract count from XMM count_reg
    UINT size = REG_Size((REG)count_reg);
    UINT8* count_val = new UINT8[size];
    PIN_GetContextRegval(pin_ctx, (REG)count_reg, count_val);
    UINT32 count = *(UINT32 *)count_val;
    printLog("value of extracted count: %u\n", count);
    // Zero the dst if count > 15
    if(count > 15)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < XMM_BITS/WORD_BITS; i++)
            *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < XMM_BITS/WORD_BITS; i++)
            *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count)) |
                (*(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) >> 
                    (BYTE_ALIGN(count) + BYTE_BITS));
    
    // Zero upper 128 bits
    thread_ctx->vcpu.avx[dst][1] = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}

/* Shift taint right of each packed word in an XMM register to the left by 
 * count bits. If count > 15, zero the taint
 *      t[dst[0:15]] = t[dst[0:15]] >> count
 *      ...
 *  AVX version: upper bits are zeroed
 * @ dst: XMM register 
 * @ src: XMM register
 * @ count: 128-bit memory location
 */

VOID shiftr_pw_xmm_m_bits_3op128_zero_upper(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, ADDRINT count_addr, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    //Extract count from memory
    UINT32 count = *(UINT32 *)count_addr;
    // Zero the dst if count > 15
    if(count > 15)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < XMM_BITS/WORD_BITS; i++)
            *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < XMM_BITS/WORD_BITS; i++)
            *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count)) |
                (*(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) >> 
                    (BYTE_ALIGN(count) + BYTE_BITS));
    
    // Zero upper 128 bits
    thread_ctx->vcpu.avx[dst][1] = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}


/* Shift taint left of each packed dword in an XMM register to the left by 
 * count bits. If count > 31, zero the taint
 *      t[dst[0:31]] = t[dst[0:31]] << count
 *      ...
 *  AVX version: upper bits are zeroed
 * @ dst: XMM register 
 * @ src: XMM register
 * @ count: 8-bit immediate
 */

VOID shiftl_pd_xmm_imm_bits_3op128_zero_upper(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    // Zero the dst if count > 31
    if(count > 31)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < XMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < XMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count)) |
                (*(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) << 
                    (BYTE_ALIGN(count) + BYTE_BITS));
    
    // Zero upper 128 bits
    thread_ctx->vcpu.avx[dst][1] = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}

/* Shift taint left of each packed dword in an XMM register to the left by 
 * count bits. If count > 31, zero the taint
 *      t[dst[0:31]] = t[dst[0:31]] << count
 *      ...
 *  AVX version: upper bits are zeroed
 * @ dst: XMM register 
 * @ src: XMM register
 * @ count_reg: XMM register containing the value of count 
 *      (PIN REG not vcpu index)
 * @ pin_ctx: pointer to pin CONTEXT - needed to extract count from count_reg
 */

VOID shiftl_pd_xmm_xmm_bits_3op128_zero_upper(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, UINT32 count_reg, 
        CONTEXT *pin_ctx, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    //Extract count from XMM count_reg
    UINT size = REG_Size((REG)count_reg);
    UINT8* count_val = new UINT8[size];
    PIN_GetContextRegval(pin_ctx, (REG)count_reg, count_val);
    UINT32 count = *(UINT32 *)count_val;
    printLog("value of extracted count: %u\n", count);
    // Zero the dst if count > 31
    if(count > 31)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < XMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < XMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count)) |
                (*(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) << 
                    (BYTE_ALIGN(count) + BYTE_BITS));
    
    // Zero upper 128 bits
    thread_ctx->vcpu.avx[dst][1] = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}

/* Shift taint left of each packed dword in an XMM register to the left by 
 * count bits. If count > 31, zero the taint
 *      t[dst[0:31]] = t[dst[0:31]] << count
 *      ...
 *  AVX version: upper bits are zeroed
 * @ dst: XMM register 
 * @ src: XMM register
 * @ count: 128-bit memory location
 */

VOID shiftl_pd_xmm_m_bits_3op128_zero_upper(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, ADDRINT count_addr, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    //Extract count from memory
    UINT32 count = *(UINT32 *)count_addr;
    // Zero the dst if count > 31
    if(count > 31)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < XMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < XMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count)) |
                (*(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) << 
                    (BYTE_ALIGN(count) + BYTE_BITS));
    
    // Zero upper 128 bits
    thread_ctx->vcpu.avx[dst][1] = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}

/* Shift taint right of each packed dword in an XMM register to the left by 
 * count bits. If count > 31, zero the taint
 *      t[dst[0:31]] = t[dst[0:31]] >> count
 *      ...
 *  AVX version: upper bits are zeroed
 * @ dst: XMM register 
 * @ src: XMM register
 * @ count: 8-bit immediate
 */

VOID shiftr_pd_xmm_imm_bits_3op128_zero_upper(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    // Zero the dst if count > 31
    if(count > 31)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < XMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < XMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count)) |
                (*(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) >> 
                    (BYTE_ALIGN(count) + BYTE_BITS));
    
    // Zero upper 128 bits
    thread_ctx->vcpu.avx[dst][1] = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint 0x%lx "
                "src xmm %u taint 0x%lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}

/* Shift taint right of each packed dword in an XMM register to the left by 
 * count bits. If count > 31, zero the taint
 *      t[dst[0:31]] = t[dst[0:31]] >> count
 *      ...
 *  AVX version: upper bits are zeroed
 * @ dst: XMM register 
 * @ src: XMM register
 * @ count_reg: XMM register containing the value of count 
 *      (PIN REG not vcpu index)
 * @ pin_ctx: pointer to pin CONTEXT - needed to extract count from count_reg
 */

VOID shiftr_pd_xmm_xmm_bits_3op128_zero_upper(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, UINT32 count_reg, 
        CONTEXT *pin_ctx, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    //Extract count from XMM count_reg
    UINT size = REG_Size((REG)count_reg);
    UINT8* count_val = new UINT8[size];
    PIN_GetContextRegval(pin_ctx, (REG)count_reg, count_val);
    UINT32 count = *(UINT32 *)count_val;
    printLog("value of extracted count: %u\n", count);
    // Zero the dst if count > 31
    if(count > 31)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < XMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < XMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count)) |
                (*(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) >> 
                    (BYTE_ALIGN(count) + BYTE_BITS));
    
    // Zero upper 128 bits
    thread_ctx->vcpu.avx[dst][1] = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}

/* Shift taint right of each packed dword in an XMM register to the left by 
 * count bits. If count > 31, zero the taint
 *      t[dst[0:31]] = t[dst[0:31]] >> count
 *      ...
 *  AVX version: upper bits are zeroed
 * @ dst: XMM register 
 * @ src: XMM register
 * @ count: 128-bit memory location
 */

VOID shiftr_pd_xmm_m_bits_3op128_zero_upper(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, ADDRINT count_addr, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    //Extract count from memory
    UINT32 count = *(UINT32 *)count_addr;
    // Zero the dst if count > 31
    if(count > 31)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < XMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < XMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count)) |
                (*(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) >> 
                    (BYTE_ALIGN(count) + BYTE_BITS));
    
    // Zero upper 128 bits
    thread_ctx->vcpu.avx[dst][1] = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}


/* Shift taint left of each packed qword in an XMM register to the left by 
 * count bits. If count > 63, zero the taint
 *      t[dst[0:63]] = t[dst[0:63]] << count
 *      ...
 *  AVX version: upper bits are zeroed
 * @ dst: XMM register 
 * @ src: XMM register
 * @ count: 8-bit immediate
 */

VOID shiftl_pq_xmm_imm_bits_3op128_zero_upper(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    // Zero the dst if count > 63
    if(count > 63)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < XMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < XMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count)) |
                (*(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) << 
                    (BYTE_ALIGN(count) + BYTE_BITS));
    
    // Zero upper 128 bits
    thread_ctx->vcpu.avx[dst][1] = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}

/* Shift taint left of each packed qword in an XMM register to the left by 
 * count bits. If count > 63, zero the taint
 *      t[dst[0:63]] = t[dst[0:63]] << count
 *      ...
 *  AVX version: upper bits are zeroed
 * @ dst: XMM register 
 * @ src: XMM register
 * @ count_reg: XMM register containing the value of count 
 *      (PIN REG not vcpu index)
 * @ pin_ctx: pointer to pin CONTEXT - needed to extract count from count_reg
 */

VOID shiftl_pq_xmm_xmm_bits_3op128_zero_upper(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, UINT32 count_reg, 
        CONTEXT *pin_ctx, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    //Extract count from XMM count_reg
    UINT size = REG_Size((REG)count_reg);
    UINT8* count_val = new UINT8[size];
    PIN_GetContextRegval(pin_ctx, (REG)count_reg, count_val);
    UINT32 count = *(UINT32 *)count_val;
    printLog("value of extracted count: %u\n", count);
    // Zero the dst if count > 63
    if(count > 63)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < XMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < XMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count)) |
                (*(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) << 
                    (BYTE_ALIGN(count) + BYTE_BITS));
    
    // Zero upper 128 bits
    thread_ctx->vcpu.avx[dst][1] = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}

/* Shift taint left of each packed qword in an XMM register to the left by 
 * count bits. If count > 63, zero the taint
 *      t[dst[0:63]] = t[dst[0:63]] << count
 *      ...
 *  AVX version: upper bits are zeroed
 * @ dst: XMM register 
 * @ src: XMM register
 * @ count: 128-bit memory location
 */

VOID shiftl_pq_xmm_m_bits_3op128_zero_upper(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, ADDRINT count_addr, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    //Extract count from memory
    UINT32 count = *(UINT32 *)count_addr;
    // Zero the dst if count > 63
    if(count > 63)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < XMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < XMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count)) |
                (*(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) << 
                    (BYTE_ALIGN(count) + BYTE_BITS));
    
    // Zero upper 128 bits
    thread_ctx->vcpu.avx[dst][1] = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}

/* Shift taint right of each packed qword in an XMM register to the left by 
 * count bits. If count > 63, zero the taint
 *      t[dst[0:63]] = t[dst[0:63]] >> count
 *      ...
 *  AVX version: upper bits are zeroed
 * @ dst: XMM register 
 * @ src: XMM register
 * @ count: 8-bit immediate
 */

VOID shiftr_pq_xmm_imm_bits_3op128_zero_upper(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    // Zero the dst if count > 63
    if(count > 63)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < XMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < XMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count)) |
                (*(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) >> 
                    (BYTE_ALIGN(count) + BYTE_BITS));
    
    // Zero upper 128 bits
    thread_ctx->vcpu.avx[dst][1] = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}

/* Shift taint right of each packed qword in an XMM register to the left by 
 * count bits. If count > 63, zero the taint
 *      t[dst[0:63]] = t[dst[0:63]] >> count
 *      ...
 *  AVX version: upper bits are zeroed
 * @ dst: XMM register 
 * @ src: XMM register
 * @ count_reg: XMM register containing the value of count 
 *      (PIN REG not vcpu index)
 * @ pin_ctx: pointer to pin CONTEXT - needed to extract count from count_reg
 */

VOID shiftr_pq_xmm_xmm_bits_3op128_zero_upper(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, UINT32 count_reg, 
        CONTEXT *pin_ctx, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    //Extract count from XMM count_reg
    UINT size = REG_Size((REG)count_reg);
    UINT8* count_val = new UINT8[size];
    PIN_GetContextRegval(pin_ctx, (REG)count_reg, count_val);
    UINT32 count = *(UINT32 *)count_val;
    printLog("value of extracted count: %u\n", count);
    // Zero the dst if count > 63
    if(count > 63)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < XMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < XMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count)) |
                (*(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) >> 
                    (BYTE_ALIGN(count) + BYTE_BITS));
    
    // Zero upper 128 bits
    thread_ctx->vcpu.avx[dst][1] = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}

/* Shift taint right of each packed qword in an XMM register to the left by 
 * count bits. If count > 63, zero the taint
 *      t[dst[0:63]] = t[dst[0:63]] >> count
 *      ...
 *  AVX version: upper bits are zeroed
 * @ dst: XMM register 
 * @ src: XMM register
 * @ count: 128-bit memory location
 */

VOID shiftr_pq_xmm_m_bits_3op128_zero_upper(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, ADDRINT count_addr, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    //Extract count from memory
    UINT32 count = *(UINT32 *)count_addr;
    // Zero the dst if count > 63
    if(count > 63)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < XMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < XMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count)) |
                (*(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) >> 
                    (BYTE_ALIGN(count) + BYTE_BITS));
    
    // Zero upper 128 bits
    thread_ctx->vcpu.avx[dst][1] = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}

/* Interleave low bytes of source and dst (starting with the dst) 
 * and store in the dst.
 *      t[dst[0:7] = t[dst[0:7]
 *      t[dst[8:15] = t[src[0:7]
 *      ... 
 * @ dst: XMM register 
 * @ src: XMM register
 */
VOID interleave_low_b_xmm_xmm_2op128(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[src][0])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx \n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                src, thread_ctx->vcpu.avx[src][0]);
#endif
    // move dst taint bytes to appropriate location - iterate through
    // lower half bytes backwards so don't overwrite. t[dst[2i]] =t[d[i]]
    for(int i = (BIT2BYTE(XMM_BITS) / 2) - 1; i >= 0; i--)
        *(((UINT8 *)&thread_ctx->vcpu.avx[dst]) + (2 * i)) = 
            *(((UINT8 *)&thread_ctx->vcpu.avx[dst]) + i);
    // move src bytes to dst. t[dst[2i+1]] = t[src[i]]
    for(int i = (BIT2BYTE(XMM_BITS) / 2) - 1; i >= 0; i--)
        *(((UINT8 *)&thread_ctx->vcpu.avx[dst]) + (2 * i) + 1) = 
            *(((UINT8 *)&thread_ctx->vcpu.avx[src]) + i);

#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm: %u taint %lx  "
                "src xmm %u taint %lx \n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                src, thread_ctx->vcpu.avx[src][0]);
#endif
}

/* Interleave low bytes of source and dst (starting with the dst) 
 * and store in the dst.
 *      t[dst[0:7] = t[dst[0:7]
 *      t[dst[8:15] = t[src[0:7]
 *      ... 
 * @ dst: XMM register 
 * @ src: 128-bit memory location
 */
VOID interleave_low_b_xmm_m_2op128(thread_ctx_t *thread_ctx, 
        UINT32 dst, ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || *(uint128_t *)get_tag_address(src))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx "
                "src 0x%lx taint %lx \n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                src, *(uint128_t *)get_tag_address(src));
#endif
    // move dst taint bytes to appropriate location - iterate through
    // lower half bytes backwards so don't overwrite. t[dst[2i]] =t[d[i]]
    for(int i = (BIT2BYTE(XMM_BITS) / 2) - 1; i >= 0; i--)
        *(((UINT8 *)&thread_ctx->vcpu.avx[dst]) + (2 * i)) = 
            *(((UINT8 *)&thread_ctx->vcpu.avx[dst]) + i);
    // move src bytes to dst. t[dst[2i+1]] = t[src[i]]
    for(int i = (BIT2BYTE(XMM_BITS) / 2) - 1; i >= 0; i--)
        *(((UINT8 *)&thread_ctx->vcpu.avx[dst]) + (2 * i) + 1) = 
            *(((UINT8 *)get_tag_address(src)) + i);

#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx \n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                src, thread_ctx->vcpu.avx[src][0]);
#endif
}

/* Interleave low words of source and dst (starting with the dst) 
 * and store in the dst.
 *      t[dst[0:15] = t[dst[0:15]
 *      t[dst[16:31] = t[src[0:15]
 *      ... 
 * @ dst: XMM register 
 * @ src: XMM register
 */
VOID interleave_low_w_xmm_xmm_2op128(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[src][0])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx \n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                src, thread_ctx->vcpu.avx[src][0]);
#endif
    // move dst taint bytes to appropriate location - iterate through
    // lower half bytes backwards so don't overwrite. t[dst[2i]] =t[d[i]]
    for(int i = (BIT2WORD(XMM_BITS) / 2) - 1; i >= 0; i--)
        *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + (2 * i)) = 
            *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i);
    // move src bytes to dst. t[dst[2i+1]] = t[src[i]]
    for(int i = (BIT2WORD(XMM_BITS) / 2) - 1; i >= 0; i--)
        *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + (2 * i) + 1) = 
            *(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i);

#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx \n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                src, thread_ctx->vcpu.avx[src][0]);
#endif
}

/* Interleave low bytes of source and dst (starting with the dst) 
 * and store in the dst.
 *      t[dst[0:15] = t[dst[0:15]
 *      t[dst[16:31] = t[src[0:15]
 *      ... 
 * @ dst: XMM register 
 * @ src: 128-bit memory location
 */
VOID interleave_low_w_xmm_m_2op128(thread_ctx_t *thread_ctx, 
        UINT32 dst, ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || *(uint128_t *)get_tag_address(src))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx "
                "src 0x%lx taint %lx \n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                src, *(uint128_t *)get_tag_address(src));
#endif
    // move dst taint bytes to appropriate location - iterate through
    // lower half bytes backwards so don't overwrite. t[dst[2i]] =t[d[i]]
    for(int i = (BIT2WORD(XMM_BITS) / 2) - 1; i >= 0; i--)
        *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + (2 * i)) = 
            *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i);
    // move src bytes to dst. t[dst[2i+1]] = t[src[i]]
    for(int i = (BIT2WORD(XMM_BITS) / 2) - 1; i >= 0; i--)
        *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + (2 * i) + 1) = 
            *(((UINT16 *)get_tag_address(src)) + i);

#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx \n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                src, thread_ctx->vcpu.avx[src][0]);
#endif
}


/* 
 * Shuffle bytes in dst according to indexes in src. Each byte in src serves
 * as the index for the corresponding byte in dst. 
 *  
 *  If the index byte is tainted, taint the corresponding dst byte. 
 *  Else if the highest bit of the src index byte is set, zero the tag. 
 *  Else move the corresponding taint tag from dst to its new index in dst.
 *
 * @ dst: XMM register 
 * @ src: XMM register
 * @ src_reg: XMM register (Pin register index, not vcpu index)
 * @ pin_ctx: Pin context - to retrieve value in src register to get 
 *      indexes for tags
 */
VOID shuf_b_xmm_xmm_2op128(thread_ctx_t *thread_ctx, UINT32 dst,
        UINT32 src, UINT32 src_reg, CONTEXT *pin_ctx, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[src][0])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx "
                "src xmm: %u taint %lx \n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                src, thread_ctx->vcpu.avx[src][0]);
#endif
    //Extract count from XMM count_reg
    UINT size = REG_Size((REG)src_reg);
    UINT8* indexes = new UINT8[size];
    PIN_GetContextRegval(pin_ctx, (REG)src_reg, indexes);
    
    uint128_t dst_tag = thread_ctx->vcpu.avx[dst][0];

    // iterate through each byte
    for(UINT8 i=0; i < BIT2BYTE(XMM_BITS); i++)
    {
        
        // If the index byte is tainted, taint the dst byte
        if(*(((UINT8 *)&thread_ctx->vcpu.avx[src]) + i))
            *(((UINT8 *)&thread_ctx->vcpu.avx[dst]) + i) = TAG_ALL8; 

        // Else if highest bit set, zero tag
        else if(HIGH_BIT_SET &indexes[i])
            *(((UINT8 *)&thread_ctx->vcpu.avx[dst]) + i) = TAG_ZERO;
        
        // Else move the tag
        else
        {
            UINT8 index = LOW4BITS_MASK & indexes[i];
            *(((UINT8 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT8 *)&dst_tag) + index);
        }
    }

#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx "
                "src xmm: %u taint %lx \n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                src, thread_ctx->vcpu.avx[src][0]);
#endif
}

/* 
 * Shuffle bytes in src1 according to indexes in src2 and store
 * in dst. Each byte in src2 serves
 * as the index for the corresponding byte in src1. 
 *  
 *  If the index byte is tainted, taint the corresponding dst byte. 
 *  Else if the highest bit of the src index byte is set, zero the tag. 
 *  Else move the corresponding taint tag from dst to its new index in dst.
 *
 *  AVX version: zero upper 128 bits
 *
 * @ dst: XMM register 
 * @ src1: XMM register
 * @ src2: XMM register - contains indexes
 * @ src2_reg: XMM register (Pin register index, not vcpu index)
 * @ pin_ctx: Pin context - to retrieve value in src register to get 
 *      indexes for tags
 */
VOID shuf_b_xmm_xmm_3op128_zero_upper(thread_ctx_t *thread_ctx, UINT32 dst,
        UINT32 src1, UINT32 src2, UINT32 src2_reg, 
        CONTEXT *pin_ctx, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[src1][0] ||
            thread_ctx->vcpu.avx[src2][0])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx "
                "src1 xmm: %u taint %lx src2 xmm: %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                src1, thread_ctx->vcpu.avx[src1][0],
                src2, thread_ctx->vcpu.avx[src2][0]);
#endif
    //Extract count from XMM count_reg
    UINT size = REG_Size((REG)src2_reg);
    UINT8* indexes = new UINT8[size];
    PIN_GetContextRegval(pin_ctx, (REG)src2_reg, indexes);
    
    // iterate through each byte
    for(UINT8 i=0; i < BIT2BYTE(XMM_BITS); i++)
    {
        
        // If the index byte is tainted, taint the dst byte
        if(*(((UINT8 *)&thread_ctx->vcpu.avx[src2]) + i))
            *(((UINT8 *)&thread_ctx->vcpu.avx[dst]) + i) = TAG_ALL8; 

        // Else if highest bit set, zero tag
        else if(HIGH_BIT_SET &indexes[i])
            *(((UINT8 *)&thread_ctx->vcpu.avx[dst]) + i) = TAG_ZERO;
        
        // Else move the tag
        else
        {
            UINT8 index = LOW4BITS_MASK & indexes[i];
            *(((UINT8 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT8 *)&thread_ctx->vcpu.avx[src1]) + index);
        }
    }

#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm: %u taint %lx  "
                "src1 xmm: %u taint %lx src2 xmm: %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                src1, thread_ctx->vcpu.avx[src1][0],
                src2, thread_ctx->vcpu.avx[src2][0]);
#endif
}

/* 
 * Shuffle bytes in src according to 2-bit indexes in the imm8
 * order operand and store in dst. Each 2-bit value in order serves
 * as the index for the where to copy the dword from src1 from.
 *
 *      t[dst[0:31]] = t[src[0:order[0:1]]]
 *      ...   
 *
 * @ dst: XMM register 
 * @ src: XMM register
 * @ order: imm8 containing 2-bit indexes
 */
VOID shuf_dw_xmm_xmm_3op128(thread_ctx_t *thread_ctx, UINT32 dst,
        UINT32 src, UINT64 order, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[src][0])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx "
                "src xmm: %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                src, thread_ctx->vcpu.avx[src][0]);
#endif
    UINT8 index_iter = order, current_index;
    
    // iterate through each dword
    for(UINT8 i=0; i < BIT2DWORD(XMM_BITS); i++)
    {
        current_index = index_iter & LOW2BITS_MASK;
        *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
            *(((UINT32 *)&thread_ctx->vcpu.avx[src]) + current_index);
        
        // Update index so low 2 bits are index for next dword
        index_iter = index_iter >> 2;
    }

#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm: %u taint %lx  "
                "src xmm: %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                src, thread_ctx->vcpu.avx[src][0]);
#endif
}

/* 
 * Shuffle bytes in src according to 2-bit indexes in the imm8
 * order operand and store in dst. Each 2-bit value in order serves
 * as the index for the where to copy the dword from src1 from.
 *
 *      t[dst[0:31]] = t[src[0:order[0:1]]]
 *      ...   
 * AVX version: zero upper 128 bits of dst ymm register
 * @ dst: XMM register 
 * @ src: XMM register
 * @ order: imm8 containing 2-bit indexes
 */
VOID shuf_dw_xmm_xmm_3op128_zero_upper(thread_ctx_t *thread_ctx, UINT32 dst,
        UINT32 src, UINT64 order, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[src][0])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx "
                "src xmm: %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                src, thread_ctx->vcpu.avx[src][0]);
#endif
    UINT8 index_iter = order, current_index;
    
    // iterate through each dword
    for(UINT8 i=0; i < BIT2DWORD(XMM_BITS); i++)
    {
        current_index = index_iter & LOW2BITS_MASK;
        *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
            *(((UINT32 *)&thread_ctx->vcpu.avx[src]) + current_index);
        
        // Update index so low 2 bits are index for next dword
        index_iter = index_iter >> 2;
    }

    // zero upper 128 bits
    thread_ctx->vcpu.avx[dst][1] = 0;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm: %u taint %lx  "
                "src xmm: %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                src, thread_ctx->vcpu.avx[src][0]);
#endif
}

/*
 * multiplies one qword from the src dst operand. bit 0 of the imm8
 * operand determines the dst qword, bit 4 the src. if the bit is 0, 
 * the low qword is selected, else the high. take the union of the taints
 * of the two selected qwords.
 * @ dst: xmm register
 * @ src: xmm register
 * @ index: 8-bit immediate
 */
void pmulqdq_xmm_2op128(thread_ctx_t *thread_ctx, UINT32 dst,
        UINT32 src, UINT64 index, UINT32 opcode)
{
#ifdef propagation_debug
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[src][0])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prepropflag && tainted)
        printlog("pre %s: dst xmm %u taint %lx "
                "src xmm: %u taint %lx\n",
                opcode_stringshort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                src, thread_ctx->vcpu.avx[src][0]);
#endif
    UINT64 tmp_tag;
    // high qword from dst
    if(index & BIT0MASK)
        // high qword from src
        if(index & BIT4MASK)
            tmp_tag = 
                *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + 1) |
                *(((UINT64 *)&thread_ctx->vcpu.avx[src]) + 1);
        //low qword from src
        else
            tmp_tag = 
                *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + 1) |
                *((UINT64 *)&thread_ctx->vcpu.avx[src]);
    // low qword from dst
    else 
        // high qword from src
        if(index & BIT4MASK)
            tmp_tag = 
                *((UINT64 *)&thread_ctx->vcpu.avx[dst]) |
                *(((UINT64 *)&thread_ctx->vcpu.avx[src]) + 1);
        //low qword from src
        else
            tmp_tag = 
                *((UINT64 *)&thread_ctx->vcpu.avx[dst]) |
                *(((UINT64 *)&thread_ctx->vcpu.avx[src]));
    *(UINT64 *)&thread_ctx->vcpu.avx[dst] = tmp_tag;
    *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + 1) = tmp_tag; 
#ifdef propagation_debug
    if(postpropflag && tainted)
        printlog("post %s: dst xmm: %u taint %lx  "
                "src xmm: %u taint %lx\n",
                opcode_stringshort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                src, thread_ctx->vcpu.avx[src][0]);
#endif
}

/*
 * multiplies one qword from the src dst operand. bit 0 of the imm8
 * operand determines the dst qword, bit 4 the src. if the bit is 0, 
 * the low qword is selected, else the high. take the union of the taints
 * of the two selected qwords.
 * @ dst: xmm register
 * @ src: 128-bit memory location
 * @ index: 8-bit immediate
 */
void pmulqdq_m_2op128(thread_ctx_t *thread_ctx, UINT32 dst,
        ADDRINT src, UINT32 index, UINT32 opcode)
{
#ifdef propagation_debug
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || *(uint128_t *)get_tag_address(src))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prepropflag && tainted)
        printlog("pre %s: dst xmm %u taint %lx "
                "src: %lx taint %lx\n",
                opcode_stringshort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                src, *(uint128_t *)get_tag_address(src));
#endif
    UINT64 tmp_tag;
    // high qword from dst
    if(index & BIT0MASK)
        // high qword from src
        if(index & BIT4MASK)
            tmp_tag = 
                *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + 1) |
                *(((UINT64 *)get_tag_address(src)) + 1);
        //low qword from src
        else
            tmp_tag = 
                *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + 1) |
                *((UINT64 *)get_tag_address(src));
    // low qword from dst
    else 
        // high qword from src
        if(index & BIT4MASK)
            tmp_tag = 
                *((UINT64 *)&thread_ctx->vcpu.avx[dst]) |
                *(((UINT64 *)get_tag_address(src)) + 1);
        //low qword from src
        else
            tmp_tag = 
                *((UINT64 *)&thread_ctx->vcpu.avx[dst]) |
                *(((UINT64 *)get_tag_address(src)));
    *(UINT64 *)&thread_ctx->vcpu.avx[dst] = tmp_tag;
    *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + 1) = tmp_tag; 
#ifdef propagation_debug
    if(postpropflag && tainted)
        printlog("post %s: dst xmm: %u taint %lx  "
                "src: %lx taint %lx\n",
                opcode_stringshort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                src, *(uint128_t *)get_tag_address(src));
#endif
}


/*
 * Copies a dword from the src operand to the destination operand at the 
 * location specified by the low 2 bits of the index operand. The taint tag 
 * of copied dword is also copied to that location in the dst taint.
 *      t[dst[(index[0:1] * 32):((index[0:1] * 32) + 31)] = t[src] 
 * @ dst: XMM register
 * @ src: 32-bit register
 * @ index: 8-bit immediate
 */
VOID pinsrd_r_2op128(thread_ctx_t *thread_ctx, UINT32 dst,
        UINT32 src, UINT64 index, UINT32 opcode)
{
#ifdef propagation_debug
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.gpr[src])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prepropflag && tainted)
        printlog("pre %s: dst xmm %u taint %lx "
                "src reg: %u taint %lx\n",
                opcode_stringshort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                src, thread_ctx->vcpu.gpr[src]);
#endif
    UINT32 i = index & LOW2BITS_MASK;
    *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
        *(UINT32 *)&thread_ctx->vcpu.gpr[src]; 
#ifdef propagation_debug
    if(postpropflag && tainted)
        printlog("post %s: dst xmm: %u taint %lx  "
                "src reg: %u taint %lx\n",
                opcode_stringshort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                src, thread_ctx->vcpu.gpr[src]);
#endif
}
 
VOID pinsrd_m_2op128(thread_ctx_t *thread_ctx, UINT32 dst,
        ADDRINT src, UINT64 index, UINT32 opcode)
{
    if(thread_ctx->vcpu.avx[dst][0] || *(UINT32 *)get_tag_address(src))
        printLog("pinsrd m TOUCHES TAINTED DATA\n");
}
 


// ymm registers////////////////////////////////////////////////////////////

/* Propagate taint from 256 bit YMM register to another YMM 
 * register with form:
 *      t[dst] = t[src]
 * @ src: YMM reg
 * @ dst: YMM reg
 * NOTE: uint_256 is typedef uint8_t[32]
 */

VOID ymm2ymm_xfer_2op256(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(ymm_reg_get_taint(thread_ctx, src) || 
            ymm_reg_get_taint(thread_ctx, dst))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src ymm: %u - taint 0x%x \
                dst ymm: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, ymm_reg_get_taint(thread_ctx, src),
                dst, ymm_reg_get_taint(thread_ctx, dst));
#endif
	memcpy((void *)thread_ctx->vcpu.avx[dst], 
            (void *)thread_ctx->vcpu.avx[src], sizeof(uint256_t));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src ymm: %u - taint 0x%x \
                dst ymm: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, ymm_reg_get_taint(thread_ctx, src),
                dst, ymm_reg_get_taint(thread_ctx, dst));
#endif
}

/* Propagate taint from 256 bit memory location to another YMM 
 * register with form:
 *      t[dst] = t[src]
 * @ src: 256-bit memory location
 * @ dst: YMM reg
 */

VOID m2ymm_xfer_2op256(thread_ctx_t *thread_ctx, UINT32 dst, 
        ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(ymm_mem_get_taint(src) || 
            ymm_reg_get_taint(thread_ctx, dst))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src ymm mem: 0x%x - taint 0x%x \
                dst ymm: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, ymm_mem_get_taint(src),
                dst, ymm_reg_get_taint(thread_ctx, dst));
#endif
	memcpy((void *)thread_ctx->vcpu.avx[dst], (void *)get_tag_address(src), 
            sizeof(uint256_t));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src ymm mem: 0x%x - taint 0x%x \
                dst ymm: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, ymm_mem_get_taint(src),
                dst, ymm_reg_get_taint(thread_ctx, dst));
#endif
}


/* Propagate taint from an YMM register to a 256-bit memory location
 * register with form:
 *      t[dst] = t[src]
 * @ src: 256-bit memory location
 * @ dst: YMM reg
 */

VOID ymm2m_xfer_2op256(thread_ctx_t *thread_ctx, ADDRINT dst, 
        UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(ymm_reg_get_taint(thread_ctx, src) || ymm_mem_get_taint(dst))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src ymm: %u - taint %s \
                dst ymm mem: 0x%x - taint %s\n",
                OPCODE_StringShort(opcode).c_str(),
                src, uint256_hex_string((uint256_t *)thread_ctx->vcpu.avx[src]).c_str(),
                dst, uint256_hex_string((uint256_t *)get_tag_address(dst)).c_str());
#endif
        
    memcpy((void *)get_tag_address(dst), (void *)thread_ctx->vcpu.avx[src], 
            sizeof(uint256_t));

#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src ymm: %u - taint 0x%x \
                dst ymm mem: 0x%x - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, ymm_reg_get_taint(thread_ctx, src),
                dst, ymm_mem_get_taint(dst));
#endif
}

/* Propagate taint from 256 bit YMM register to another YMM 
 * register with form:
 *      t[dst] |= t[src]
 * @ src: YMM reg
 * @ dst: YMM reg
 */

VOID ymm2ymm_union_2op256(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(ymm_reg_get_taint(thread_ctx, src) || 
            ymm_reg_get_taint(thread_ctx, dst))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src ymm: %u - taint 0x%x \
                dst ymm: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, ymm_reg_get_taint(thread_ctx, src),
                dst, ymm_reg_get_taint(thread_ctx, dst));
#endif
	thread_ctx->vcpu.avx[dst][0] |=  
        thread_ctx->vcpu.avx[src][0];
	thread_ctx->vcpu.avx[dst][1] |=  
        thread_ctx->vcpu.avx[src][1];
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src ymm: %u - taint 0x%x \
                dst ymm: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, ymm_reg_get_taint(thread_ctx, src),
                dst, ymm_reg_get_taint(thread_ctx, dst));
#endif
}

/* Propagate taint from 256 bit memory location to another YMM 
 * register with form:
 *      t[dst] |= t[src]
 * @ src: 256-bit memory location
 * @ dst: YMM reg
 */

VOID m2ymm_union_2op256(thread_ctx_t *thread_ctx, UINT32 dst, 
        ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(ymm_mem_get_taint(src) || ymm_reg_get_taint(thread_ctx, dst))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src ymm: %u - taint 0x%x \
                dst ymm: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, ymm_mem_get_taint(src),
                dst, ymm_reg_get_taint(thread_ctx, dst));
#endif
	thread_ctx->vcpu.avx[dst][0] |=  
        *(uint128_t *)get_tag_address(src);
	thread_ctx->vcpu.avx[dst][1] |=  
        *(uint128_t *)(get_tag_address(src) + sizeof(uint128_t));

#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src ymm: %u - taint 0x%x \
                dst ymm: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, ymm_mem_get_taint(src),
                dst, ymm_reg_get_taint(thread_ctx, dst));
#endif
}


/* Propagate taint from an YMM register to a 256-bit memory location
 * register with form:
 *      t[dst] |= t[src]
 * @ src: 256-bit memory location
 * @ dst: YMM reg
 */

VOID ymm2m_union_2op256(thread_ctx_t *thread_ctx, ADDRINT dst, 
        UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(ymm_reg_get_taint(thread_ctx, src) || ymm_mem_get_taint(dst))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Post %s: src ymm: %u - taint 0x%x \
                dst ymm: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, ymm_reg_get_taint(thread_ctx, src),
                dst, ymm_mem_get_taint(dst));
#endif
	*(uint128_t *)get_tag_address(dst) |=  
        thread_ctx->vcpu.avx[src][0];
	*(uint128_t *)(get_tag_address(dst) + sizeof(uint128_t)) |=
        thread_ctx->vcpu.avx[src][1];
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src ymm: %u - taint 0x%x \
                dst ymm: %u - taint %u\n",
                OPCODE_StringShort(opcode).c_str(),
                src, ymm_reg_get_taint(thread_ctx, src),
                dst, ymm_mem_get_taint(dst));
#endif
}

/* Propagate taint from two 256 bit YMM registers to another YMM 
 * register with form:
 *      t[dst] = t[src1] | t[src2]
 * @ dst: YMM reg
 * @ src1: YMM reg
 * @ src2: YMM reg
 */

VOID ymm_ymm2ymm_src_union_3op256(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src1, UINT32 src2, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(ymm_reg_get_taint(thread_ctx, src1) || 
            ymm_reg_get_taint(thread_ctx, src2) || 
            ymm_reg_get_taint(thread_ctx, src2)) 
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src1 ymm: %u - taint %lu \
                src2 ymm: %u taint: %lu dst ymm: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src1, ymm_reg_get_taint(thread_ctx, src1),
                src2, ymm_reg_get_taint(thread_ctx, src2),
                dst, ymm_reg_get_taint(thread_ctx, dst));
#endif
	*(uint128_t *)&thread_ctx->vcpu.avx[dst] = 
        *(uint128_t *)&thread_ctx->vcpu.avx[src1] | 
        *(uint128_t *)&thread_ctx->vcpu.avx[src2];
	*(((uint128_t *)&thread_ctx->vcpu.avx[dst]) + 1 ) = 
        *(((uint128_t *)&thread_ctx->vcpu.avx[src1]) + 1) | 
        *(((uint128_t *)&thread_ctx->vcpu.avx[src2]) + 1);

#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src1 ymm: %u - taint %lu \
                src2 ymm: %u taint: %lu dst ymm: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src1, ymm_reg_get_taint(thread_ctx, src1),
                src2, ymm_reg_get_taint(thread_ctx, src2),
                dst, ymm_reg_get_taint(thread_ctx, dst));
#endif
}

/* Propagate taint from a 256 bit YMM register (ymm1) and a 256-bit memory 
 * location to another YMM register (ymm2) with form:
 *      t[dst] = t[src1] | t[src2]
 * @ dst: YMM2 reg
 * @ src1: YMM1 reg
 * @ src2: 256-bit memory location
 */

VOID ymm_m2ymm_src_union_3op256(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src1, UINT32 src2, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(ymm_reg_get_taint(thread_ctx, src1) || 
            ymm_mem_get_taint(src2) || 
            ymm_reg_get_taint(thread_ctx, src2)) 
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src1 ymm: %u - taint %lu \
                src2 ymm: %u taint: %lu dst ymm: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src1, ymm_reg_get_taint(thread_ctx, src1),
                src2, ymm_mem_get_taint(src2),
                dst, ymm_reg_get_taint(thread_ctx, dst));
#endif
	*(uint128_t *)&thread_ctx->vcpu.avx[dst] = 
        *(uint128_t *)&thread_ctx->vcpu.avx[src1] | 
        *(uint128_t *)get_tag_address(src2);
	*(((uint128_t *)&thread_ctx->vcpu.avx[dst]) + 1 ) = 
        *(((uint128_t *)&thread_ctx->vcpu.avx[src1]) + 1) | 
        *(((uint128_t *)get_tag_address(src2)) + 1);

#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src1 ymm: %u - taint %lu \
                src2 ymm: %u taint: %lu dst ymm: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src1, ymm_reg_get_taint(thread_ctx, src1),
                src2, ymm_mem_get_taint(src2),
                dst, ymm_reg_get_taint(thread_ctx, dst));
#endif
}

/* Propagate taint from a YMM register to the lower dword of a 32/64-bit gpr. 
 * The taint for the low 32 bits of the dst is the union of all corresponding 
 * source taint bytes.
 *      t[dst_[0:7]] = t[src[0:7]] | ... | t[src[56:63]] (bytes 0-7)
 *      t[dst_[8:15]] = t[src[64:71]] | ... | t[src[120:127]] (bytes 8-15)
 *      t[dst_[16:23]] = t[src[128:135]] | ... | t[src[184:191]] (bytes 16-23)
 *      t[dst_[24:31]] = t[src[192:199]] | ... | t[src[248:255]] (bytes 24-31)
 *  The upper bits are zeroed
 * @ src: XMM register 
 * @ dst: gpr register
 */

VOID ymm2r_xfer_op32_zero_upper(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(*(UINT64 *)&thread_ctx->vcpu.avx[src] || thread_ctx->vcpu.gpr[dst])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: src xmm: %u - taint %lu \
                dst gpr: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(UINT64 *)&thread_ctx->vcpu.avx[src],
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
    // compute first taint byte
    UINT8 tmp_tag = 0;
    for(int i = 0; i < 8; i++)
        tmp_tag |= *(((UINT8 *)&thread_ctx->vcpu.avx[src]) + i);
    *(UINT8 *)&thread_ctx->vcpu.gpr[dst] = tmp_tag;
    
    // compute second taint byte
    tmp_tag = 0;
    for(int i = 8; i < 16; i++)
        tmp_tag |= *(((UINT8 *)&thread_ctx->vcpu.avx[src]) + i);
    *(((UINT8 *)&thread_ctx->vcpu.gpr[dst]) + 1) = tmp_tag;
    
    // compute third taint byte
    tmp_tag = 0;
    for(int i = 16; i < 24; i++)
        tmp_tag |= *(((UINT8 *)&thread_ctx->vcpu.avx[src]) + i);
    *(((UINT8 *)&thread_ctx->vcpu.gpr[dst]) + 2) = tmp_tag;
    
    // compute fourth taint byte
    tmp_tag = 0;
    for(int i = 24; i < 32; i++)
        tmp_tag |= *(((UINT8 *)&thread_ctx->vcpu.avx[src]) + i);
    *(((UINT8 *)&thread_ctx->vcpu.gpr[dst]) + 3) = tmp_tag;

    // Zero upper 32 bytes
	*(((UINT32 *)&thread_ctx->vcpu.gpr[dst]) + 1) = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: src xmm %u taint %lx "
                "dst gpr: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                src, *(UINT64 *)&thread_ctx->vcpu.avx[src],
                dst, thread_ctx->vcpu.gpr[dst]);
#endif
}


/* Shift taint left of each packed word in an YMM register to the left by 
 * count bits. If count > 15, zero the taint
 *      t[dst[0:15]] = t[dst[0:15]] << count
 *      ...
 * @ dst: YMM register 
 * @ src: YMM register
 * @ count: 8-bit immediate
 */

VOID shiftl_pw_ymm_imm_bits_3op256(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    // Zero the dst if count > 15
    if(count > 15)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < YMM_BITS/WORD_BITS; i++)
            *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < YMM_BITS/WORD_BITS; i++)
            *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count)) |
                (*(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) << 
                    (BYTE_ALIGN(count) + BYTE_BITS));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}

/* Shift taint left of each packed word in an YMM register to the left by 
 * count bits. If count > 15, zero the taint
 *      t[dst[0:15]] = t[dst[0:15]] << count
 *      ...
 * @ dst: YMM register 
 * @ src: YMM register
 * @ count_reg: YMM register containing the value of count 
 *      (PIN REG not vcpu index)
 * @ pin_ctx: pointer to pin CONTEXT - needed to extract count from count_reg
 */

VOID shiftl_pw_ymm_ymm_bits_3op256(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, UINT32 count_reg, 
        CONTEXT *pin_ctx, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    //Extract count from XMM count_reg
    UINT size = REG_Size((REG)count_reg);
    UINT8* count_val = new UINT8[size];
    PIN_GetContextRegval(pin_ctx, (REG)count_reg, count_val);
    UINT32 count = *(UINT32 *)count_val;
    printLog("value of extracted count: %u\n", count);
    // Zero the dst if count > 15
    if(count > 15)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < YMM_BITS/WORD_BITS; i++)
            *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < YMM_BITS/WORD_BITS; i++)
            *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count)) |
                (*(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) << 
                    (BYTE_ALIGN(count) + BYTE_BITS));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}

/* Shift taint left of each packed word in an YMM register to the left by 
 * count bits. If count > 15, zero the taint
 *      t[dst[0:15]] = t[dst[0:15]] << count
 *      ...
 * @ dst: YMM register 
 * @ src: YMM register
 * @ count: 128-bit memory location
 */

VOID shiftl_pw_ymm_m_bits_3op256(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, ADDRINT count_addr, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    //Extract count from memory
    UINT32 count = *(UINT32 *)count_addr;
    // Zero the dst if count > 15
    if(count > 15)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < YMM_BITS/WORD_BITS; i++)
            *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < YMM_BITS/WORD_BITS; i++)
            *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count)) |
                (*(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) << 
                    (BYTE_ALIGN(count) + BYTE_BITS));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}

/* Shift taint right of each packed word in an YMM register to the left by 
 * count bits. If count > 15, zero the taint
 *      t[dst[0:15]] = t[dst[0:15]] >> count
 *      ...
 * @ dst: YMM register 
 * @ src: YMM register
 * @ count: 8-bit immediate
 */

VOID shiftr_pw_ymm_imm_bits_3op256(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    // Zero the dst if count > 15
    if(count > 15)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < YMM_BITS/WORD_BITS; i++)
            *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < YMM_BITS/WORD_BITS; i++)
            *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count)) |
                (*(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) >> 
                    (BYTE_ALIGN(count) + BYTE_BITS));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}

/* Shift taint right of each packed word in an YMM register to the left by 
 * count bits. If count > 15, zero the taint
 *      t[dst[0:15]] = t[dst[0:15]] >> count
 *      ...
 * @ dst: YMM register 
 * @ src: YMM register
 * @ count_reg: YMM register containing the value of count 
 *      (PIN REG not vcpu index)
 * @ pin_ctx: pointer to pin CONTEXT - needed to extract count from count_reg
 */

VOID shiftr_pw_ymm_ymm_bits_3op256(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, UINT32 count_reg, 
        CONTEXT *pin_ctx, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    //Extract count from XMM count_reg
    UINT size = REG_Size((REG)count_reg);
    UINT8* count_val = new UINT8[size];
    PIN_GetContextRegval(pin_ctx, (REG)count_reg, count_val);
    UINT32 count = *(UINT32 *)count_val;
    printLog("value of extracted count: %u\n", count);
    // Zero the dst if count > 15
    if(count > 15)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < YMM_BITS/WORD_BITS; i++)
            *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < YMM_BITS/WORD_BITS; i++)
            *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count)) |
                (*(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) >> 
                    (BYTE_ALIGN(count) + BYTE_BITS));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}

/* Shift taint right of each packed word in an YMM register to the left by 
 * count bits. If count > 15, zero the taint
 *      t[dst[0:15]] = t[dst[0:15]] >> count
 *      ...
 * @ dst: YMM register 
 * @ src: YMM register
 * @ count: 128-bit memory location
 */

VOID shiftr_pw_ymm_m_bits_3op256(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, ADDRINT count_addr, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    //Extract count from memory
    UINT32 count = *(UINT32 *)count_addr;
    // Zero the dst if count > 15
    if(count > 15)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < YMM_BITS/WORD_BITS; i++)
            *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < YMM_BITS/WORD_BITS; i++)
            *(((UINT16 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count)) |
                (*(((UINT16 *)&thread_ctx->vcpu.avx[src]) + i) >> 
                    (BYTE_ALIGN(count) + BYTE_BITS));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}

/* Shift taint left of each packed dword in an YMM register to the left by 
 * count bits. If count > 31, zero the taint
 *      t[dst[0:31]] = t[dst[0:31]] << count
 *      ...
 * @ dst: YMM register 
 * @ src: YMM register
 * @ count: 8-bit immediate
 */

VOID shiftl_pd_ymm_imm_bits_3op256(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    // Zero the dst if count > 31
    if(count > 31)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < YMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < YMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count)) |
                (*(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) << 
                    (BYTE_ALIGN(count) + BYTE_BITS));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}

/* Shift taint left of each packed dword in an YMM register to the left by 
 * count bits. If count > 31, zero the taint
 *      t[dst[0:31]] = t[dst[0:31]] << count
 *      ...
 * @ dst: YMM register 
 * @ src: YMM register
 * @ count_reg: YMM register containing the value of count 
 *      (PIN REG not vcpu index)
 * @ pin_ctx: pointer to pin CONTEXT - needed to extract count from count_reg
 */

VOID shiftl_pd_ymm_ymm_bits_3op256(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, UINT32 count_reg, 
        CONTEXT *pin_ctx, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    //Extract count from YMM count_reg
    UINT size = REG_Size((REG)count_reg);
    UINT8* count_val = new UINT8[size];
    PIN_GetContextRegval(pin_ctx, (REG)count_reg, count_val);
    UINT32 count = *(UINT32 *)count_val;
    printLog("value of extracted count: %u\n", count);
    // Zero the dst if count > 31
    if(count > 31)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < YMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < YMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count)) |
                (*(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) << 
                    (BYTE_ALIGN(count) + BYTE_BITS));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}

/* Shift taint left of each packed dword in an YMM register to the left by 
 * count bits. If count > 31, zero the taint
 *      t[dst[0:31]] = t[dst[0:31]] << count
 *      ...
 * @ dst: YMM register 
 * @ src: YMM register
 * @ count: 128-bit memory location
 */

VOID shiftl_pd_ymm_m_bits_3op256(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, ADDRINT count_addr, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    //Extract count from memory
    UINT32 count = *(UINT32 *)count_addr;
    // Zero the dst if count > 31
    if(count > 31)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < YMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < YMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count)) |
                (*(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) << 
                    (BYTE_ALIGN(count) + BYTE_BITS));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}

/* Shift taint right of each packed dword in an YMM register to the left by 
 * count bits. If count > 31, zero the taint
 *      t[dst[0:31]] = t[dst[0:31]] >> count
 *      ...
 * @ dst: YMM register 
 * @ src: YMM register
 * @ count: 8-bit immediate
 */

VOID shiftr_pd_ymm_imm_bits_3op256(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    // Zero the dst if count > 31
    if(count > 31)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < YMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < YMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count)) |
                (*(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) >> 
                    (BYTE_ALIGN(count) + BYTE_BITS));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}

/* Shift taint right of each packed dword in an YMM register to the left by 
 * count bits. If count > 31, zero the taint
 *      t[dst[0:31]] = t[dst[0:31]] >> count
 *      ...
 * @ dst: YMM register 
 * @ src: YMM register
 * @ count_reg: YMM register containing the value of count 
 *      (PIN REG not vcpu index)
 * @ pin_ctx: pointer to pin CONTEXT - needed to extract count from count_reg
 */

VOID shiftr_pd_ymm_ymm_bits_3op256(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, UINT32 count_reg, 
        CONTEXT *pin_ctx, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    //Extract count from YMM count_reg
    UINT size = REG_Size((REG)count_reg);
    UINT8* count_val = new UINT8[size];
    PIN_GetContextRegval(pin_ctx, (REG)count_reg, count_val);
    UINT32 count = *(UINT32 *)count_val;
    printLog("value of extracted count: %u\n", count);
    // Zero the dst if count > 31
    if(count > 31)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < YMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < YMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count)) |
                (*(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) >> 
                    (BYTE_ALIGN(count) + BYTE_BITS));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}

/* Shift taint right of each packed dword in an YMM register to the left by 
 * count bits. If count > 31, zero the taint
 *      t[dst[0:31]] = t[dst[0:31]] >> count
 *      ...
 * @ dst: YMM register 
 * @ src: YMM register
 * @ count: 128-bit memory location
 */

VOID shiftr_pd_ymm_m_bits_3op256(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, ADDRINT count_addr, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    //Extract count from memory
    UINT32 count = *(UINT32 *)count_addr;
    // Zero the dst if count > 31
    if(count > 31)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < YMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < YMM_BITS/DWORD_BITS; i++)
            *(((UINT32 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count)) |
                (*(((UINT32 *)&thread_ctx->vcpu.avx[src]) + i) >> 
                    (BYTE_ALIGN(count) + BYTE_BITS));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}

/* Shift taint left of each packed qword in an YMM register to the left by 
 * count bits. If count > 63, zero the taint
 *      t[dst[0:63]] = t[dst[0:63]] << count
 *      ...
 * @ dst: YMM register 
 * @ src: YMM register
 * @ count: 8-bit immediate
 */

VOID shiftl_pq_ymm_imm_bits_3op256(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    // Zero the dst if count > 63
    if(count > 63)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < YMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < YMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count)) |
                (*(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) << 
                    (BYTE_ALIGN(count) + BYTE_BITS));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}

/* Shift taint left of each packed qword in an YMM register to the left by 
 * count bits. If count > 63, zero the taint
 *      t[dst[0:63]] = t[dst[0:63]] << count
 *      ...
 * @ dst: YMM register 
 * @ src: YMM register
 * @ count_reg: YMM register containing the value of count 
 *      (PIN REG not vcpu index)
 * @ pin_ctx: pointer to pin CONTEXT - needed to extract count from count_reg
 */

VOID shiftl_pq_ymm_ymm_bits_3op256(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, UINT32 count_reg, 
        CONTEXT *pin_ctx, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    //Extract count from YMM count_reg
    UINT size = REG_Size((REG)count_reg);
    UINT8* count_val = new UINT8[size];
    PIN_GetContextRegval(pin_ctx, (REG)count_reg, count_val);
    UINT32 count = *(UINT32 *)count_val;
    printLog("value of extracted count: %u\n", count);
    // Zero the dst if count > 63
    if(count > 63)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < YMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < YMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count)) |
                (*(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) << 
                    (BYTE_ALIGN(count) + BYTE_BITS));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}

/* Shift taint left of each packed qword in an YMM register to the left by 
 * count bits. If count > 63, zero the taint
 *      t[dst[0:63]] = t[dst[0:63]] << count
 *      ...
 * @ dst: YMM register 
 * @ src: YMM register
 * @ count: 128-bit memory location
 */

VOID shiftl_pq_ymm_m_bits_3op256(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, ADDRINT count_addr, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    //Extract count from memory
    UINT32 count = *(UINT32 *)count_addr;
    // Zero the dst if count > 63
    if(count > 63)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < YMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < YMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) << BYTE_ALIGN(count)) |
                (*(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) << 
                    (BYTE_ALIGN(count) + BYTE_BITS));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}

/* Shift taint right of each packed qword in an YMM register to the left by 
 * count bits. If count > 63, zero the taint
 *      t[dst[0:63]] = t[dst[0:63]] >> count
 *      ...
 * @ dst: YMM register 
 * @ src: YMM register
 * @ count: 8-bit immediate
 */

VOID shiftr_pq_ymm_imm_bits_3op256(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    // Zero the dst if count > 63
    if(count > 63)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < YMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < YMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count)) |
                (*(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) >> 
                    (BYTE_ALIGN(count) + BYTE_BITS));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}

/* Shift taint right of each packed qword in an YMM register to the left by 
 * count bits. If count > 63, zero the taint
 *      t[dst[0:63]] = t[dst[0:63]] >> count
 *      ...
 * @ dst: YMM register 
 * @ src: YMM register
 * @ count_reg: YMM register containing the value of count 
 *      (PIN REG not vcpu index)
 * @ pin_ctx: pointer to pin CONTEXT - needed to extract count from count_reg
 */

VOID shiftr_pq_ymm_ymm_bits_3op256(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, UINT32 count_reg, 
        CONTEXT *pin_ctx, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    //Extract count from YMM count_reg
    UINT size = REG_Size((REG)count_reg);
    UINT8* count_val = new UINT8[size];
    PIN_GetContextRegval(pin_ctx, (REG)count_reg, count_val);
    UINT32 count = *(UINT32 *)count_val;
    printLog("value of extracted count: %u\n", count);
    // Zero the dst if count > 63
    if(count > 63)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < YMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < YMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count)) |
                (*(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) >> 
                    (BYTE_ALIGN(count) + BYTE_BITS));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}

/* Shift taint right of each packed qword in an YMM register to the left by 
 * count bits. If count > 63, zero the taint
 *      t[dst[0:63]] = t[dst[0:63]] >> count
 *      ...
 * @ dst: YMM register 
 * @ src: YMM register
 * @ count: 128-bit memory location
 */

VOID shiftr_pq_ymm_m_bits_3op256(thread_ctx_t *thread_ctx, 
        UINT32 dst, UINT32 src, ADDRINT count_addr, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] || 
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
    //Extract count from memory
    UINT32 count = *(UINT32 *)count_addr;
    // Zero the dst if count > 63
    if(count > 63)
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
    // Else shift each word by count bits, whole byte shift so no overlaps
    else if(count % 8 == 0)
        for(int i = 0; i < YMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                *(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count);
    // Else shift each word by count bits, overlapping byte tags 
    else
        for(int i = 0; i < YMM_BITS/QWORD_BITS; i++)
            *(((UINT64 *)&thread_ctx->vcpu.avx[dst]) + i) = 
                (*(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) >> BYTE_ALIGN(count)) |
                (*(((UINT64 *)&thread_ctx->vcpu.avx[src]) + i) >> 
                    (BYTE_ALIGN(count) + BYTE_BITS));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst ymm: %u taint %lx %lx "
                "src ymm %u taint %lx %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0],
                thread_ctx->vcpu.avx[src][1]);
#endif
}


/* Shift taint left of upper and lower dqword in a YMM register to the left by 
 * count bytes.
 *      t[dst[0:127]] = t[src[0:127]] << (count * 8)
 *      t[dst[128:255]] = t[src[128:255]] << (count * 8)
 * @ dst: YMM register 
 * @ src: YMM register
 * @ count: 8-bit immediate
 */

VOID shiftl_pdq_ymm_imm_bytes_3op256(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src, UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] ||
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0], thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0], thread_ctx->vcpu.avx[src][1]);
#endif
    // Zero the dst if count > 15
    if(count > 15)
    {
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
        thread_ctx->vcpu.avx[dst][1] = TAG_ZERO;
    }
    else
    {
        thread_ctx->vcpu.avx[dst][0] = 
            thread_ctx->vcpu.avx[src][0] << (BIT2BYTE(count));
        thread_ctx->vcpu.avx[dst][1] = 
            thread_ctx->vcpu.avx[src][1] << (BIT2BYTE(count));
    }

#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0], thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0], thread_ctx->vcpu.avx[src][1]);
#endif
}

/* Shift taint right of upper and lower dqword in a YMM register to the left by 
 * count bytes.
 *      t[dst[0:127]] = t[src[0:127]] >> (count * 8)
 *      t[dst[128:255]] = t[src[128:255]] >> (count * 8)
 * @ dst: YMM register 
 * @ src: YMM register
 * @ count: 8-bit immediate
 */

VOID shiftr_pdq_ymm_imm_bytes_3op256(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src, UINT64 count, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if(thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[dst][1] ||
            thread_ctx->vcpu.avx[src][0] || thread_ctx->vcpu.avx[src][1])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0], thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0], thread_ctx->vcpu.avx[src][1]);
#endif
    // Zero the dst if count > 15
    if(count > 15)
    {
        thread_ctx->vcpu.avx[dst][0] = TAG_ZERO;
        thread_ctx->vcpu.avx[dst][1] = TAG_ZERO;
    }
    else
    {
        thread_ctx->vcpu.avx[dst][0] = 
            thread_ctx->vcpu.avx[src][0] >> (BIT2BYTE(count));
        thread_ctx->vcpu.avx[dst][1] = 
            thread_ctx->vcpu.avx[src][1] >> (BIT2BYTE(count));
    }

#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm %u taint %lx "
                "src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0], thread_ctx->vcpu.avx[dst][1],
                src, thread_ctx->vcpu.avx[src][0], thread_ctx->vcpu.avx[src][1]);
#endif
}


// INS specific analysis functions ////////////////////////////////////////////

/* Taint propagation for the syscall function:
 * t[RCX] = zero (loaded with RIP)
 * t[R11] = zero (loaded with RFLAGS)
 */
VOID handle_syscall(thread_ctx_t *thread_ctx, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if( thread_ctx->vcpu.gpr[RCX] || thread_ctx->vcpu.gpr[R11])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: RCX: %u - taint %lu R11: %u - taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                thread_ctx->vcpu.gpr[RCX],
                thread_ctx->vcpu.gpr[R11]);
#endif
    thread_ctx->vcpu.gpr[RCX] = TAG_ZERO;
    thread_ctx->vcpu.gpr[R11] = TAG_ZERO;
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: RCX taint %lu R11 taint %lu\n",
                OPCODE_StringShort(opcode).c_str(),
                thread_ctx->vcpu.gpr[RCX],
                thread_ctx->vcpu.gpr[R11]);
#endif
}

/* Taint propagation for vzeroupper: zero the taints of the
 * upper 128 bits of all ymm registers
 */
VOID handle_vzeroupper(thread_ctx_t *thread_ctx, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    for(UINT8 i = 0; i < AVX_NUM; i++)
    {
        if(thread_ctx->vcpu.avx[i][1])
        {
            tainted = 1; 
            break;
        }
    }
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    // too many taints to print...
#endif
    for(UINT8 i = 0; i < AVX_NUM; i++)
    {
        thread_ctx->vcpu.avx[i][1] = TAG_ZERO;
    }
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: cleared taint of upper 128 bits of all "
                "YMM regs\n",
                OPCODE_StringShort(opcode).c_str());
#endif
}

/* Reverse the byte order of the taint tags
 * @ dst: 32 or 64-bit register 
 * @ reg_width: width of register in bits
 */
VOID bswap(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 reg_width, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if( thread_ctx->vcpu.gpr[dst])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst reg: %u - taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                thread_ctx->vcpu.gpr[dst]);
#endif
    UINT64 tmp_tag = thread_ctx->vcpu.gpr[dst];
    UINT32 reg_bytes = BIT2BYTE(reg_width);
    for(UINT8 i = 0; i < reg_bytes; i++)
        *(((UINT8 *)&thread_ctx->vcpu.gpr) + i) = 
                    *(((UINT8 *)&tmp_tag) + (reg_bytes - 1 - i));
#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst reg %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                thread_ctx->vcpu.gpr[dst]);
#endif
}


/* Compares packed strings and sets ECX. Set taint of ECX to union of 
 * all taint tags in both src operands
 *      t[ECX] = t[dst] | t[src] 
 * @ dst: XMM reg
 * @ src: XMM reg
 */
VOID handle_pcmpistri_xmm(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if( thread_ctx->vcpu.avx[dst][0] || thread_ctx->vcpu.avx[src][0])
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm: %u - taint %lx src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                src, thread_ctx->vcpu.avx[src][0]);
#endif
    UINT8 tmp_tag = 0;
    for(UINT8 i = 0; i < BIT2BYTE(XMM_BITS); i++)
        tmp_tag |= 
            *(((UINT8 *)&thread_ctx->vcpu.avx[dst]) + i) | 
            *(((UINT8 *)&thread_ctx->vcpu.avx[src]) + i);
    *(((UINT8 *)&thread_ctx->vcpu.gpr[RCX])) = tmp_tag; 
    *(((UINT8 *)&thread_ctx->vcpu.gpr[RCX]) + 1) = tmp_tag; 
    *(((UINT8 *)&thread_ctx->vcpu.gpr[RCX]) + 2) = tmp_tag; 
    *(((UINT8 *)&thread_ctx->vcpu.gpr[RCX]) + 3) = tmp_tag; 
    
    //zero upper 32 bits of ECX
    *(((UINT32 *)&thread_ctx->vcpu.gpr[RCX]) + 1) = TAG_ZERO;    

#ifdef PROPAGATION_DEBUG
    if(postPropFlag && tainted)
        printLog("Post %s: dst xmm: %u - taint %lx src xmm %u taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                src, thread_ctx->vcpu.avx[src][0]);
#endif
}

/* Compares packed strings and sets ECX. Set taint of ECX to union of 
 * all taint tags in both src operands
 *      t[ECX] = t[dst] | t[src] 
 * @ dst: XMM reg
 * @ src: 128-bit memory location
 */
VOID handle_pcmpistri_m(thread_ctx_t *thread_ctx, UINT32 dst, 
        ADDRINT src, UINT32 opcode)
{
#ifdef PROPAGATION_DEBUG
    int tainted = 0;
    if( thread_ctx->vcpu.avx[dst][0] || *(uint128_t *)get_tag_address(src))
        tainted = 1; 
#ifdef ALL_ANALYSIS_DEBUG
tainted=1;
#endif
    if(prePropFlag && tainted)
        printLog("Pre %s: dst xmm: %u - taint %lx src: 0x%lx taint %lx\n",
                OPCODE_StringShort(opcode).c_str(),
                dst, thread_ctx->vcpu.avx[dst][0],
                src, *(uint128_t *)get_tag_address(src));
#endif
    UINT8 tmp_tag = 0;
    ADDRINT src_tag_address = get_tag_address(src);
    printLog("pcmpistri mem src addr: 0x%lx tag addr: 0x%lx tag: 0x%lx %lx\n",
            src, src_tag_address, *(UINT64 *)get_tag_address(src), 
            *((UINT64 *)get_tag_address(src) + 64));
    for(UINT8 i = 0; i < BIT2BYTE(XMM_BITS); i++)
    {
        UINT8 union_tag =
            *(((UINT8 *)&thread_ctx->vcpu.avx[dst]) + i) | 
            *(((UINT8 *)src_tag_address) + i);
        tmp_tag |= union_tag;
        /*printLog("%u: dst: %x src %x union: %x\n",
                i, *(((UINT8 *)&thread_ctx->vcpu.avx[dst]) + i),
                *(((UINT8 *)src_tag_address) + i), union_tag);*/
    }
    *(((UINT8 *)&thread_ctx->vcpu.gpr[RCX])) = tmp_tag; 
    *(((UINT8 *)&thread_ctx->vcpu.gpr[RCX]) + 1) = tmp_tag; 
    *(((UINT8 *)&thread_ctx->vcpu.gpr[RCX]) + 2) = tmp_tag; 
    *(((UINT8 *)&thread_ctx->vcpu.gpr[RCX]) + 3) = tmp_tag; 
    //zero upper 32 bits of ECX
    *(((UINT32 *)&thread_ctx->vcpu.gpr[RCX]) + 1) = TAG_ZERO;    
#ifdef PROPAGATION_DEBUG
    pretty_print_taint(thread_ctx, opcode, tainted, 3, POST, GPR64, RCX, XMM, dst, M128, src);
#endif
}

/*Lazy functions to test if touch tainted data 
 */
VOID cvtsi2sd_r2xmm(thread_ctx_t *thread_ctx, UINT32 dst, 
        UINT32 src, UINT32 opcode)
{
    if(thread_ctx->vcpu.avx[dst][1] || thread_ctx->vcpu.gpr[src])
        printLog("%s r2xmm TOUCHES TAINTED DATA\n",
                OPCODE_StringShort(opcode).c_str());
}

VOID cvtsi2sd_m32_2xmm(thread_ctx_t *thread_ctx, UINT32 dst, 
        ADDRINT src, UINT32 opcode)
{
    if(thread_ctx->vcpu.avx[dst][1] || *(UINT32 *)get_tag_address(src))
        printLog("%s m32 TOUCHES TAINTED DATA\n",
                OPCODE_StringShort(opcode).c_str());
}

VOID cvtsi2sd_m64_2xmm(thread_ctx_t *thread_ctx, UINT32 dst, 
        ADDRINT src, UINT32 opcode)
{
    if(thread_ctx->vcpu.avx[dst][1] || *(UINT64 *)get_tag_address(src))
        printLog("%s m64 TOUCHES TAINTED DATA\n",
                OPCODE_StringShort(opcode).c_str());
}

//Declassifcation

void //PIN_FAST_ANALYSIS_CALL
save_declassify_length(ADDRINT addr)
{
    printLog("in save declassify_length analysis func, length at 0x%lx\n", addr);
    declassify_length = *(unsigned int *)addr;
    printLog("saved declassify length of %u\n", declassify_length);

}

VOID declassify(ADDRINT addr)
{
#ifdef DEBUG
    printLog("in declassify, buffer at 0x%lx\n", addr);
    //sanity checks
    //1. We should have a length
    if(declassify_length <= 0)
    {
        printLog("WARNING: declassify length <=0\n");
    }
    assert(declassify_length > 0);

    //2. is memory actually tainted?
    ADDRINT tainted = mem_is_tainted(addr, declassify_length);
    if(tainted)
        printLog("Declassify sanity check: %ld bytes are tainted at addr 0x%lx\n", 
            declassify_length, addr);
    else
        printLog("WARNING: memory to declassify is not tainted\n");
#endif

    tagmap_clrn(addr, declassify_length);

    tainted = mem_is_tainted(addr, declassify_length);
    assert(!tainted);
    //reset length
    declassify_length = 0;
    
}

VOID check_taint(ADDRINT addr){
    ADDRINT tainted = mem_is_tainted(addr, declassify_length);
    printLog("Taint check of %d bytes at 0x%lx: %s\n", 
        declassify_length, addr, tainted?"yes":"no");
    //printPageAndByteTaints();
}

VOID print_taint(){
    printLog("Printing all tainted pages and bytes\n");
    printPageAndByteTaints();
}


