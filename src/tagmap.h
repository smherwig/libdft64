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

#ifndef __TAGMAP_H__
#define __TAGMAP_H__

#include <unordered_map>


#include "pin.H"

///////// New 64-bit defs ////////////////////////

//#define UNUSED_ADDR_BITS 16
//#define USABLE_ADDR(vaddr >> UNUSED_ADDR_BITS) 

// Virtual address memory layout in x_64_86
#define USER_START  0x0U
#define USER_END    0x00007FFFFFFFFFFFU
#define KERN_START  0xFFFF800000000000U
#define KERN_END    0xFFFFFFFFFFFFFFFFU

#define STAB_KERN   0xFFFF800000000000U


/* maximum size on an entry in /proc/<pid>/maps */
#define MAPS_ENTRY_MAX	256
/* maximum size on an entry in /proc/self/maps */
#define PROC_MAPS_PATH "/proc/self/maps"
// Constant strings to find mappings in /proc/self/maps
#define STACK_MAP_STR   "[stack]"
#define VDSO_MAP_STR    "[vdso]"
#define DYNLDLNK_STR        "/lib/x86_64-linux-gnu/ld-2.24.so" //entry in proc/maps
//dynamic linker/loader
#define	DYNLDLNK	"/lib64/ld-linux-x86-64.so.2"//IMG name loaded by elf_load
#define HEAP_MAP_STR        "[heap]"

/* tag values */
#define	TAG_ZERO    0x0U		/* clean		*/
#define	TAG_ALL8    0xFFU		/* all colors; 1 byte	*/

// Flags to specify if new tagmap mapping should be taintable and thus
// allocate new taint tag pages, or untataintable and thus map to the
// read-only zero_seg
#define UNTAINTABLE 0
#define TAINTABLE 1

// Flags to specify if taint tag pages should be deallocated in 
// remove_mapping_from_tagmap
#define DEALLOCATE 1
#define NO_DEALLOCATE 0 
/*
 * In 32-bit libdft, the entire STAB was a preallocated array,
 * possible because it was a reasonable size:
 *      32-bit ptr * 1<<20 pages of addressable mem = 4MB
 * With 64-bit addresses, this would be much too large:
 *      64-bit ptr * 1<<36 pages addressable mem = 512GB (!!)
 *        *36 = 48 bits used for address - 12-bit page offset
 */


#define IN_KERNEL_SPACE(vaddr) (vaddr >= KERN_START)

#define PAGE_SHIFT	12		/* page alignment offset (bits) */
/* page align a virtual address					*/
#define PAGE_ALIGN(vaddr)	((vaddr) & 0xFFFFFFFFFFFFF000)

#define TOTAL_ADDR_BITS 48

#define NUM_L1_BITS 16
#define L1_BITMASK 0xFFFF00000000U
#define NUM_L1_ENTRIES (1UL << NUM_L1_BITS)
#define L1_INDX_BITS(vaddr) ((vaddr & L1_BITMASK) >> (TOTAL_ADDR_BITS - NUM_L1_BITS))
#define L1_ALIGN(vaddr) (vaddr && L1_BITMASK)

#define NUM_L2_BITS (TOTAL_ADDR_BITS - NUM_L1_BITS - PAGE_SHIFT)
#define L2_BITMASK 0x0000FFFFF000U
#define L2_INDX_BITS(vaddr) ((vaddr & L2_BITMASK) >> PAGE_SHIFT)
#define NUM_L2_ENTRIES (1UL << NUM_L2_BITS)
#define L2_ALIGN(vaddr) (vaddr && L2_BITMASK)
#define L2_SIZE (NUM_L2_ENTRIES * sizeof(ADDRINT))

extern ADDRINT TAGMAP_L1[NUM_L1_ENTRIES];
typedef ADDRINT *tagmap_l2_t;
extern ADDRINT KERNEL_TAINT_PAGE;
extern int NUM_L2_ALLOCS;
extern void *zero_seg;

// Old 32-bit defs
#if 0
#define PAGE_SHIFT	12		/* page alignment offset (bits) */
#define PAGE_SZ		(1U << PAGE_SHIFT)	/* page size;
					   4 KB in x86 (i386) Linux	*/
#define STACK_SZ	(PAGE_SZ << 11)		/* stack size;
					   8 MB in x86 (i386) Linux	*/
#define STAB_SIZE	(1U << 20)	/* 1 M items; 4GB / PAGE_SZ	*/
#define USER_START	0x00000000U	/* userland starting address	*/
#define USER_END	0xBFFFFFFFU	/* userland ending address	*/
#define KERN_START	0xC0000000U	/* kernel starting address	*/
#define KERN_END	0xFFFFFFFFU	/* kernel ending address	*/
#define STACK_SEG_ADDR	(KERN_START - STACK_SZ)	/* 0xBF800000		*/

/* maximum size on an entry in /proc/<pid>/maps */
#define MAPS_ENTRY_MAX	128
/* vDSO string in /proc/<pid>/maps */
#define VDSO_STR	"[vdso]"
/* dynamic linker/loader					*/
#define	DYNLDLNK	"/lib/ld-linux.so.2"

/* get the offset on stlb given a virtual address		*/
#define VIRT2STAB(vaddr)	((vaddr) >> PAGE_SHIFT)
/* get the virtual address (page aligned) given an stlb offset	*/
#define STAB2VIRT(indx)		((indx) << PAGE_SHIFT)
/* page align a virtual address					*/
#define PAGE_ALIGN(vaddr)	((vaddr) & 0xFFFFF000)
#endif



/* tagmap API */
int			                        tagmap_alloc(void);
void		PIN_FAST_ANALYSIS_CALL	tagmap_setb(ADDRINT, uint8_t);
void		PIN_FAST_ANALYSIS_CALL	tagmap_clrb(ADDRINT);
uint8_t		                        tagmap_getb(ADDRINT);

void		PIN_FAST_ANALYSIS_CALL	tagmap_setw(ADDRINT, uint16_t);
void		PIN_FAST_ANALYSIS_CALL	tagmap_clrw(ADDRINT);
uint16_t	                        tagmap_getw(ADDRINT);

void		PIN_FAST_ANALYSIS_CALL	tagmap_setl(ADDRINT, uint32_t);
void		PIN_FAST_ANALYSIS_CALL	tagmap_clrl(ADDRINT);
UINT32	    PIN_FAST_ANALYSIS_CALL	tagmap_getl(ADDRINT);

void		PIN_FAST_ANALYSIS_CALL	tagmap_setll(ADDRINT, UINT64);
void		PIN_FAST_ANALYSIS_CALL	tagmap_clrll(ADDRINT);
UINT64	    PIN_FAST_ANALYSIS_CALL	tagmap_getll(ADDRINT);

void tagmap_setn(ADDRINT, ADDRINT, uint8_t);
void					            tagmap_clrn(ADDRINT, ADDRINT);
void					            tagmap_clrn_debug(ADDRINT, ADDRINT);

#if 0
void PIN_FAST_ANALYSIS_CALL ins_clrb(ADDRINT, UINT32);
void PIN_FAST_ANALYSIS_CALL ins_clrw(ADDRINT, UINT32);
void PIN_FAST_ANALYSIS_CALL ins_clrl(ADDRINT, UINT32);
void PIN_FAST_ANALYSIS_CALL ins_clrll(ADDRINT, UINT32);
void PIN_FAST_ANALYSIS_CALL ins_clrn(ADDRINT, UINT32, UINT32);
ADDRINT get_tag_address(ADDRINT);
#endif

ADDRINT mem_is_tainted(ADDRINT, ADDRINT);
VOID add_mapping_to_tagmap(ADDRINT, ADDRINT, int, void*);
VOID remove_mapping_from_tagmap(ADDRINT, UINT, int);

uint128_t ymm_reg_get_taint(thread_ctx_t *, UINT32);
uint128_t ymm_mem_get_taint(ADDRINT);

#endif /* __TAGMAP_H__ */
