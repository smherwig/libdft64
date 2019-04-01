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

#include <sys/mman.h>
#include <stdlib.h>
#include <errno.h>
#include <limits.h>
#include <string.h>
#include <iostream>
#include <assert.h>
#include <set>
#include <unistd.h>

#include "libdft_api.h"
#include "tagmap.h"
#include "branch_pred.h"
#include "libdft_instrument.h"

#ifdef	HUGE_TLB
#ifndef	MAP_HUGETLB
#define	MAP_HUGETLB	0x40000	/* architecture specific */
#endif
#define MAP_FLAGS	MAP_PRIVATE | MAP_ANONYMOUS | MAP_HUGETLB
#else
#define MAP_FLAGS	MAP_PRIVATE | MAP_ANONYMOUS
#endif

// static function definitions
static ADDRINT get_tag_address(ADDRINT);

/*
 * tagmap
 *
 * the tagmap is the data structure that keeps tag information for the virtual
 * address space of a process. In the 32-bit x86 architecture (i386), it is
 * implemented using tagmap segments of PAGE_SIZE bytes. We assign a tagmap
 * segment to each chunk in the virtual address space that is PAGE_SIZE bytes,
 * and the mapping is done byte-to-byte (i.e., every addressable byte has a
 * ``shadow'' byte in its corresponding tagmap segment that can hold up to 8
 * different tags)
 */

/*
 * STAB
 *
 * the segment table (STAB) keeps the necessary information for translating
 * virtual addresses to their ``shadowed'' addresses. In the 32-bit x86
 * architecture (i386), it is implemented using a single level page-table-like
 * structure with 4 GB/PAGE_SIZE entries. Each entry, translates all the
 * addresses of a PAGE_SIZE chunk to their shadowed bytes in a tagmap segment,
 * and the translation is performed as follows:
 *
 * 	taddr = vaddr + STAB[vaddr >> lg(PAGE_SIZE)]
 *
 */


/* program break */
ADDRINT brk_start	= 0;
ADDRINT	brk_end		= 0;

void *zero_seg = NULL;

// init global vars
int NUM_L2_ALLOCS = 0;
ADDRINT KERNEL_TAINT_PAGE = 0;
ADDRINT TAGMAP_L1[NUM_L1_ENTRIES] = {0};

/*
 * track when the dynamic linker/loader
 * is loaded into the address space of
 * the process (flag)
 */
static
size_t dynldlnk_loaded	= 0;

NATIVE_PID get_NATIVE_PID_CURRENT(){
	NATIVE_PID pid;
	OS_GetPid(&pid);
	return pid;
}

/* Allocates a new L2 tagmap array at the provided page address and
 * stores a pointer to this l2 array in the corresponding L1 tagmap entry
 */
VOID allocate_l2(ADDRINT page_start, VOID **new_l2)
{
#ifdef DEBUG_MEMTRACK
    printLog("about to allocate new_l2 size %d (%d bits: %u entries * %ld). "
            "new_l2 currently %p\n", 
            L2_SIZE, NUM_L2_BITS, NUM_L2_ENTRIES, sizeof(ADDRINT), *new_l2);
#endif
    OS_RETURN_CODE ret = OS_AllocateMemory(NATIVE_PID_CURRENT,
                        OS_PAGE_PROTECTION_TYPE_READ | 
                        OS_PAGE_PROTECTION_TYPE_WRITE |
                        ~OS_PAGE_PROTECTION_TYPE_EXECUTE,
                        L2_SIZE, OS_MEMORY_FLAGS_PRIVATE, new_l2);
    if(!OS_RETURN_CODE_IS_SUCCESS(ret))
    {
        printLog("allocating l2 array failed\n");
        libdft_die();
    }

    memset(*new_l2, 0, L2_SIZE);

    TAGMAP_L1[L1_INDX_BITS(page_start)] = (ADDRINT) *new_l2;

#ifdef DEBUG
    NUM_L2_ALLOCS++;
    printLog("Allocated new L2 array for vaddr %p at L1 indx 0x%x"
            " Total L2 arrays allocated: %d\n", page_start, 
            L1_INDX_BITS(page_start), NUM_L2_ALLOCS);
#endif
}

/* Allocates a new taint tag segment
 * @ len: length in bytes of the segment
 * @ seg_ptr: pointer to pointer to taint tag segement to be allocated
 */
void allocate_taint_segment(UINT32 len, VOID **seg_ptr)
{
    OS_RETURN_CODE ret = OS_AllocateMemory(NATIVE_PID_CURRENT,
                        OS_PAGE_PROTECTION_TYPE_READ | 
                        OS_PAGE_PROTECTION_TYPE_WRITE | 
                        ~OS_PAGE_PROTECTION_TYPE_EXECUTE,
                        len, OS_MEMORY_FLAGS_PRIVATE, seg_ptr);
    if(!OS_RETURN_CODE_IS_SUCCESS(ret))
    {
        printLog("allocating taint segment failed: %s\n", ret);
        libdft_die();
    }
#ifdef DEBUG_MEMTRACK
        printLog("allocated new taint seg of size %x at %p\n",
                len, *seg_ptr);
#endif

    memset(*seg_ptr, 0, len);
}


/* When the process allocates new memory, call this function to allocate
 * and map the corresponding taint tag shadow memory.
 */
VOID add_mapping_to_tagmap(ADDRINT start, ADDRINT end, int can_be_tainted, 
        void *preallocated_tseg)
{
    if(start >= KERN_START)
    {
        return;
    }
    
    VOID *taint_tag_segment = NULL;
    tagmap_l2_t l2 = NULL;
    ADDRINT tagmap_offset = 0;
#ifdef DEBUG_MEMTRACK
    printLog("adding mapping [0x%lx - 0x%lx]\n", start, end);
#endif

    // segment can be tainted. Allocate new taint pages and add mapping to 
    // tagmap
    if(can_be_tainted == TAINTABLE)
    {
        // get the size of the segment, page-aligned since we only allocate
        // full pages
        //FIXME: Are mappings page aligned?
        if(PAGE_ALIGN(start) != start)
        {
            printLog("TAGMAP ERROR: segment start not page aligned\n");
            tagmap_l2_t l2 = (tagmap_l2_t)TAGMAP_L1[L1_INDX_BITS(start)];
            if(l2 != NULL && l2[L2_INDX_BITS(start)] != 0)
            {
                printLog("start taint page already allocated\n");
                start = PAGE_ALIGN(start) + PAGE_SIZE;
            }
            else{
                printLog("start taint page not already allocated\n");
                start = PAGE_ALIGN(start);
            }
        }
        if(PAGE_ALIGN(end) != end)
        {
#ifdef DEBUG_MEMTRACK
            printLog("segment end not page aligned\n");
#endif
            tagmap_l2_t l2 = (tagmap_l2_t)TAGMAP_L1[L1_INDX_BITS(end)];
            if(l2 != NULL && l2[L2_INDX_BITS(end)] != 0)
            {
#ifdef DEBUG_MEMTRACK
                printLog("end taint page already allocated\n");
#endif
                end  = PAGE_ALIGN(end);
            }
            else
            {
                end = PAGE_ALIGN(end) + PAGE_SIZE;
            }
        }

        //normal case
        ADDRINT mapping_size = end - start;
        if (start >=end)
        {
#ifdef DEBUG_MEMTRACK
            printLog("nothing to allocate\n");
#endif
            return;
        }

        //TODO: This assumes if first page is already allocated, entire
        //segment is already allocated. Is this safe?
        l2 = (tagmap_l2_t) TAGMAP_L1[L1_INDX_BITS(start)];
        if(!preallocated_tseg && l2 && l2[L2_INDX_BITS(start)])
        {
#ifdef DEBUG
                printLog("Taint page already allocated for l1[%x][%x] "
                        "-> 0x%lx\n", L1_INDX_BITS(start), 
                        L2_INDX_BITS(start), start,
                        get_tag_address(start));
#endif
                return;
        }
        
        // If taint segment not preallocated, allocate new segment
        if(!preallocated_tseg)
            allocate_taint_segment(mapping_size, &taint_tag_segment);
        else
        {
            taint_tag_segment = preallocated_tseg;
#ifdef DEBUG_MEMTRACK
            printLog("using preallocated taint segment at %p\n",
                    taint_tag_segment);
#endif
        }
      
        // compute the tag offset that will be added to the vaddr to get the 
        // tag addr. Segments are same size, so offset is constant
        tagmap_offset = (ADDRINT)taint_tag_segment - PAGE_ALIGN(start);

        // Iterate through each page of the mapping. Check the L2 array for 
        // that addr has been allocated then store the offset
        for (ADDRINT page_start = PAGE_ALIGN(start);
                page_start < PAGE_ALIGN(end);
                page_start += PAGE_SIZE)
        {
            l2 = (tagmap_l2_t) TAGMAP_L1[L1_INDX_BITS(page_start)];
#ifdef EXTRA_DEBUG_MEMTRACK
            printLog("tagmap L1[%x] = %p\n", L1_INDX_BITS(page_start), l2);
#endif
            // Allocate a new L2 array if not allocated
            if (!l2)
            {
#ifdef DEBUG_MEMTRACK
                printLog("l2 array for %x not allocated. Allocating...\n", L1_INDX_BITS(page_start));
#endif
                allocate_l2(page_start, (VOID **)&l2);
            }

            // Store the offset in the L2 tagmap array
            l2[L2_INDX_BITS(page_start)] = tagmap_offset;

#ifdef EXTRA_DEBUG_MEMTRACK
            printLog("mapped %p to offset %p tag addr %p\n", 
                    page_start, tagmap_offset, page_start + tagmap_offset);
#endif
        }
    }

    // Segment is untaintable -- map each page to zero seg
    else
    {
        
        for(ADDRINT page_start = start; 
                page_start < end; 
                page_start += PAGE_SIZE)
        {
            l2 = (tagmap_l2_t)TAGMAP_L1[L1_INDX_BITS(page_start)];
            if (!l2)
                allocate_l2(page_start, (VOID **)&l2);
			
            l2[L2_INDX_BITS(page_start)] = (ADDRINT)zero_seg - page_start;
#ifdef EXTRA_DEBUG_MEMTRACK
            printLog("mapped %p to offset %p tag addr %p\n", 
                    page_start, (ADDRINT)tseg - page_start, zero_seg);
#endif
        }
    }

#ifdef DEBUG_MEMTRACK
    printLog(string("Mapped section " + hexstr(start) + "-" + 
                hexstr(end) + " [" + hexstr(get_tag_address(start)) + "-" +
                hexstr(get_tag_address(end - 1)) + + "]\n\n").c_str());
#endif
}


/* Remove a segment from the tagmap. Don't deallocate any allocated L2 arrays,
 * but do deallocate unused taint tag pages.
 * @ seg_start: starting addr of the segment to unmap
 * @ size: length in bytes of the segment
 */
VOID remove_mapping_from_tagmap(ADDRINT unmap_start, UINT size, int deallocate_mem)
{
#ifdef DEBUG_MEMTRACK
    printLog("about to remove mapping at addr 0x%lx len 0x%x\n", unmap_start, size);
#endif
    ADDRINT end, tag_page_addr;
    end = PAGE_ALIGN(unmap_start + size) + PAGE_SIZE;
    if(unmap_start != PAGE_ALIGN(unmap_start))
    {
        printLog("ERROR: unmap segment start not page aligned: 0x%lx\n", 
                unmap_start);
        unmap_start = PAGE_ALIGN(unmap_start);
    }
    
    tag_page_addr = get_tag_address(unmap_start);

    // Only need to deallocate taint pages for writeable mapping
	if (tag_page_addr != (ADDRINT)zero_seg && deallocate_mem)
        // free the corresponding taint tag pages with PIN's memory freer
        if (unlikely(!OS_RETURN_CODE_IS_SUCCESS(
                        OS_FreeMemory(NATIVE_PID_CURRENT, 
                            (void *)(tag_page_addr),size)))) 
        {
            printLog("tagmap page deallocation failed\n");
            libdft_die();
        }

    tagmap_l2_t l2 = NULL;

    // Clear the L2 tagmap entries pointing to the freed taint pages
	for (ADDRINT page_start = unmap_start; 
            page_start < end; page_start += PAGE_SIZE) 
    {        
		l2 = (tagmap_l2_t)TAGMAP_L1[L1_INDX_BITS(page_start)];
        if(!l2){
            printLog("ERROR: trying to clear entry in l2 %x but does not exist\n", L1_INDX_BITS(page_start));
            continue;
        }
        l2[L2_INDX_BITS(page_start)] = 0;
	}
#ifdef DEBUG_MEMTRACK
			/* verbose */
			printLog((string(__func__) + ": unmapped segment [" +
				hexstr(unmap_start) + "-" + hexstr(end) +
				"]\n").c_str());
#endif
}


/* Gets the specified memory segment mapping from the proc/self/maps file and 
 * adds the memory segment to the tagmap.
 */
int add_proc_mappings_to_tagmap()
{
	
    
FILE *in, *out;
            char ch;
            in = fopen("/proc/self/maps", "r");
            out = fopen("proc_maps", "w");
            if(in == NULL || out == NULL)
                printf("error opening file\n");
            printLog("opened files\n");
            while((ch = fgetc(in)) != EOF)
                fputc(ch, out);
            fclose(in);
            fclose(out);
    
    
    
    /* file pointer */
	FILE	*fp		= NULL;
	/* path to /proc/<pid>/maps */
	char	maps_path[PATH_MAX];
	/* line buffer */
	char	lbuf[MAPS_ENTRY_MAX];
	
	/* initialization */
	ADDRINT mapping_start = 0, mapping_end = 0;
    char permissions[4];
    int taintable = 0;
	/* open /proc/self/maps */
	if ((fp = fopen(PROC_MAPS_PATH, "r")) == NULL) {
		/* failed */
		printLog((string(__func__) + ": failed while trying to open "
				+ string(maps_path) + " -- (" +
				string(strerror(errno)) + ")\n").c_str());
        return -1;
	}
	
	/* read the file */
	while(!feof(fp)) {
		/* buffer cleanup */
		memset(lbuf, 0, MAPS_ENTRY_MAX);
        mapping_start=mapping_end=0;
        memset(permissions, 0, sizeof(permissions));

		/* read a line */
		if (fgets(lbuf, MAPS_ENTRY_MAX, fp) == NULL) {
			/* something went wrong */
			if (ferror(fp)) {
				/* verbose */
				printLog((string(__func__) +
					": failed while trying to read"
					+ string(maps_path) + " -- (" +
					string(strerror(errno)) + ")\n").c_str());
				break;
			}
		}
		
	    //example file line format:
        //  7fff6601a000-7fff6603b000 rw-p 00000000 00:00 0   [stack]

        // Read in the mapping values
		sscanf(lbuf, "%lx-%lx %s %*x %*s %*u %*s\n",
				&mapping_start, &mapping_end, permissions);
        if(!mapping_start || !mapping_end)
        {
            printLog("error scanning addresses from line:\n%s\n", lbuf);
            return -1;
        }
        
        // writable mapping = taintable
        if(permissions[1] == 'w')
            taintable = TAINTABLE;
        // not writable = not taintable
        else
            taintable = UNTAINTABLE;

#ifdef DEBUG_MEMTRACK
            printLog("%s", lbuf);
            printLog("mapping: 0x%lx - 0x%lx taintable: %d\n", 
                    mapping_start, mapping_end, taintable);
#endif

        // Special case for the heap mapping - set the brk start and end
        if (strstr(lbuf, HEAP_MAP_STR) != NULL)
        {
            brk_start = mapping_start;
            brk_end = mapping_end;
            size_t heap_len = brk_end - brk_start;
            //allocate taint page with calloc so we can later realloc
            void * tseg = calloc(heap_len, 1);
#ifdef DEBUG_MEMTRACK
            printLog("Calloc'ed heap segment len %zu at %p. "
                    "brk: [0x%lx - 0x%lx]\n", heap_len, tseg, brk_start, brk_end);
#endif
            add_mapping_to_tagmap(mapping_start, mapping_end, taintable, tseg);
        }
        else
            add_mapping_to_tagmap(mapping_start, mapping_end, taintable, NULL);
	}
    fclose(fp);
    return 0;
}



/*
 * ELF image loading callback
 *
 * capture the loading of an image and setup the tagmap; we
 * allocate a tagmap segment and adjust the STAB accordingly 
 *
 * @img:	image handle
 * @v:		callback value
 */
static void
elf_load(IMG img, VOID *v)
{
	/* 
	 * after the dynamic linker/loaded is mapped into
	 * the address space of the process, the image loading
	 * is handled via mmap(2). However, we cannot unregister
	 * elf_load, so we rely on this ugly hack; optimized branch
	 */ 
	if (likely(dynldlnk_loaded == 1))
		return;

#ifdef DEBUG_MEMTRACK
	/* verbose */
	printLog((string(__func__) + ": " +
		IMG_Name(img) + " " +
		hexstr(IMG_LowAddress(img)) + "-" +
		hexstr(IMG_HighAddress(img)) + "\n").c_str());
#endif	
	
    add_mapping_to_tagmap(IMG_LowAddress(img), IMG_HighAddress(img), 
            TAINTABLE, NULL);
	
	/* check if the loaded image was the dynamic linker/loader */
	if (IMG_Name(img).compare(DYNLDLNK) == 0 ||
			IMG_Type(img) == IMG_TYPE_STATIC)
    {
		/* set the corresponding flag accordingly */
		dynldlnk_loaded = 1;
#ifdef DEBUG_MEMTRACK
        printLog("dynamic linker loaded\n");
#endif
    }
}


/*
 * initialize the STAB/tagmap
 *
 * allocate space for the STAB structure and the three ``hardcoded''
 * tagmap segments: zero_seg (PAGE_SIZE), null_seg (PAGE_SIZE), and
 * stack_seg (STACK_SZ)
 *
 * returns:	0 on success, 1 on error 
 */
int
tagmap_alloc(void)
{
    // Allocate zero_seg, a read-only taint page. Mapping pages to zero_seg
    // means that page cannot contain taint
    if(unlikely(
		//R (set to rw, zero out, then set to read only)
		!OS_RETURN_CODE_IS_SUCCESS((OS_AllocateMemory(NATIVE_PID_CURRENT,
            OS_PAGE_PROTECTION_TYPE_READ | OS_PAGE_PROTECTION_TYPE_WRITE |
            ~OS_PAGE_PROTECTION_TYPE_EXECUTE,
            (PAGE_SIZE*2), OS_MEMORY_FLAGS_PRIVATE, &zero_seg)))))
    {
		
		/* error message */
		printLog((string(__func__) +
			": tagmap segment allocation failed (" +
			string(strerror(errno)) + ")\n").c_str());
	
		/* failed */
		goto err;
	}
    
    // Zero the page, then set to read only
    memset(zero_seg, 0, PAGE_SIZE);
    OS_ProtectMemory(NATIVE_PID_CURRENT,
            zero_seg, ((PAGE_SIZE*2) - 1), 
            OS_PAGE_PROTECTION_TYPE_READ | ~OS_PAGE_PROTECTION_TYPE_WRITE |
            ~OS_PAGE_PROTECTION_TYPE_EXECUTE);
    

	/* 
	 * the kernel address space is mapped to zero_seg;
	 * this is how we handle vsyscall (i.e., reading from a
	 * kernel address will result in always reading clear tags).
     * Since mapping the whole 64-bit kernel space would require 255GB
     * and all pages map to the same taint tag page anyway, just add
     * a single STAB entry for all kernel space. 
     * TODO: This means we must first always check if the addr is in
     * kernel space -- need to check performance overhead
	 */

    KERNEL_TAINT_PAGE = (ADDRINT)zero_seg;
#ifdef DEBUG_MEMTRACK
    printLog("kernel taint page set to zero_seg at %p\n", zero_seg);
#endif

    //Clear the upper level tagmap array - stores pointers to lower level 
    //array
    memset(TAGMAP_L1, 0, NUM_L1_ENTRIES * sizeof(ADDRINT));

    // Allocate and map taint pages for process mappings from proc/maps 
    add_proc_mappings_to_tagmap(); 

    // check brk has been set, if not set
    if(!brk_end)
    {
        void *prev_brk = sbrk(0);    
        brk_start = brk_end = (ADDRINT) prev_brk;
        printLog("brk_end was not found from heap. using sbrk. brk set to %p\n", 
                brk_end);
    }


	/* register the ELF image load callback */
	IMG_AddInstrumentFunction(elf_load, NULL);
	
	/* return with success */
	return 0;

err:	/* error handling */
	
	/* cleanup */
	if (zero_seg != NULL)
		/* deallocate the zero segment space */
		OS_FreeMemory(NATIVE_PID_CURRENT, zero_seg, PAGE_SIZE);

	/* return with failure */
	return 1;
}

/*
 * tag a byte in the virtual address space
 *
 * @addr:	the virtual address
 * @color:	the tag value
 */
void PIN_FAST_ANALYSIS_CALL
tagmap_setb(size_t addr, uint8_t color)
{
	/* tag the byte that corresponds to the given address */
	*(uint8_t *)(get_tag_address(addr)) = color;
}


/*
 * untag a byte in the virtual address space
 *
 * @addr:	the virtual address
 */
void PIN_FAST_ANALYSIS_CALL
tagmap_clrb(size_t addr)
{
    /* clear the byte that corresponds to the given address */
	*(uint8_t *)(get_tag_address(addr)) = TAG_ZERO;
}

/*
 * get the tag value of a byte from the tagmap
 *
 * @addr:	the virtual address
 *
 * returns:	the tag value (e.g., 0, 1,...)
 */
uint8_t
tagmap_getb(size_t addr)
{
	/* get the byte that corresponds to the address */
	return *(uint8_t *)(get_tag_address(addr));
}

/*
 * tag a word (i.e., 2 bytes) in the virtual address space
 *
 * @addr:	the virtual address
 * @color:	the tag value
 */
void PIN_FAST_ANALYSIS_CALL
tagmap_setw(size_t addr, uint16_t color)
{
	/* tag the bytes that correspond to the addresses of the word */
	*(uint16_t *)(get_tag_address(addr)) = color;
    //print_new_tag(addr, 2, color);
}


/*
 * untag a word (i.e., 2 bytes) in the virtual address space
 *
 * @addr:	the virtual address
 */
void PIN_FAST_ANALYSIS_CALL
tagmap_clrw(size_t addr, UINT32 opcode)
{
	/* clear the bytes that correspond to the addresses of the word */
	*(uint16_t *)(get_tag_address(addr)) = TAG_ZERO;
}

/*
 * get the tag value of a word (i.e., 2 bytes) from the tagmap
 *
 * @addr:	the virtual address
 *
 * returns:	the tag value (e.g., 0, 1,...)
 */
uint16_t
tagmap_getw(size_t addr)
{
	/* get the bytes that correspond to the addresses of the word */
	return *(uint16_t *)(get_tag_address(addr));
}

/*
 * tag a long word (i.e., 4 bytes) in the virtual address space
 *
 * @addr:	the virtual address
 * @color:	the tag value
 */
void PIN_FAST_ANALYSIS_CALL
tagmap_setl(size_t addr, uint32_t color)
{
	/* tag the bytes that correspond to the addresses of the long word */
	*(uint32_t *)(get_tag_address(addr)) = color;
    //print_new_tag(addr, 4, color);
}

/*
 * untag a long word (i.e., 4 bytes) in the virtual address space
 *
 * @addr:	the virtual address
 */
void PIN_FAST_ANALYSIS_CALL
tagmap_clrl(size_t addr, UINT32 opcode)
{
	/* clear the bytes that correspond to the addresses of the long word */
	*(uint32_t *)(get_tag_address(addr)) = TAG_ZERO;
}

/*
 * get the tag value of a long word (i.e., 4 bytes) from the tagmap
 *
 * @addr:	the virtual address
 *
 * returns:	the tag value (e.g., 0, 1,...)
 */
uint32_t PIN_FAST_ANALYSIS_CALL
tagmap_getl(size_t addr)
{
	/* get the bytes that correspond to the addresses of the long word */
	return *(uint32_t *)(get_tag_address(addr));
}


/*
 * tag a long long word (i.e., 8 bytes) in the virtual address space
 *
 * @addr:	the virtual address
 * @color:	the tag value
 */
void PIN_FAST_ANALYSIS_CALL
tagmap_setll(ADDRINT addr, ADDRINT color)
{
	/* tag the bytes that correspond to the addresses of the long word */
	*(ADDRINT*)(get_tag_address(addr)) = color;
    //print_new_tag(addr, 4, color);
}

/*
 * untag a long long word (i.e., 8 bytes) in the virtual address space
 *
 * @addr:	the virtual address
 */
void PIN_FAST_ANALYSIS_CALL
tagmap_clrll(size_t addr, UINT32 opcode)
{
	/* clear the bytes that correspond to the addresses of the long word */
	*(ADDRINT *)(get_tag_address(addr)) = TAG_ZERO;
}

/*
 * get the tag value of a long long word (i.e., 8 bytes) from the tagmap
 *
 * @addr:	the virtual address
 *
 * returns:	the tag value (e.g., 0, 1,...)
 */
ADDRINT PIN_FAST_ANALYSIS_CALL
tagmap_getll(ADDRINT addr)
{
	/* get the bytes that correspond to the addresses of the long word */
	return *(ADDRINT *)(get_tag_address(addr));
}

/* tag an arbitrary number of bytes in the virtual address space
 *
 * @addr:	the virtual address
 * @num:	the number of bytes to tag
 * @color:	the tag value
 */
void
tagmap_setn(ADDRINT addr, size_t num, uint8_t color)
{
    ADDRINT tag_addr = get_tag_address(addr);
#ifdef DEBUG
    printLog("tainting %zu at vaddr 0x%lx tag addr: 0x%lx\n", num, addr, tag_addr);
#endif

	/* tag the bytes that correspond to the addresses of the num bytes */
	memset((void *)tag_addr, color, num);
}

/*
 * untag an arbitrary number of bytes in the virtual address space
 *
 * @addr:	the virtual address
 * @num:	the number of bytes to untag
 */
void
tagmap_clrn(size_t addr, size_t num)
{
#ifdef EXTRA_DEBUG_MEMTRACK
    printLog("in tagmap_clrn about to clear %u bytes at address 0x%lx tag addr: 0x%lx \n", 
            num, addr, (void *)get_tag_address(addr));
#endif
	/* clear the bytes that correspond to the addresses of the num bytes */
	memset((void *)get_tag_address(addr), TAG_ZERO, num);
#ifdef PROPAGATION_DEBUG
    if(mem_is_tainted(addr, num))
        printLog("cleared %u bytes at %p\n", num, addr);
#endif
}

/*Returns 0 if memory is not tainted. Else, returns 1
 * 
 * @addr: virtual memory addr to check for taint
 * @num: number of bytes to check
 */
ADDRINT mem_is_tainted(ADDRINT addr, ADDRINT num)
{
#ifdef EXTRA_DEBUG_MEMTRACK
    printLog("Checking if %d bytes are tainted at 0x%lx\n", num, addr);
#endif

    UINT32 bytes_checked = 0;
    while(num - bytes_checked >= sizeof(ADDRINT))
    {
        if(tagmap_getll(addr + bytes_checked))
            return 1;
        bytes_checked += sizeof(ADDRINT);
    }
    while(num - bytes_checked >= sizeof(uint32_t))
    {
        if(tagmap_getl(addr + bytes_checked))
            return 1;
        bytes_checked += sizeof(uint32_t);
    }
    while(num - bytes_checked >= sizeof(uint16_t))
    {
        if(tagmap_getw(addr + bytes_checked))
            return 1;
        bytes_checked += sizeof(uint16_t);
    }
    while(num - bytes_checked >= sizeof(uint8_t))
    {
        if(tagmap_getb(addr + bytes_checked))
            return 1;
        bytes_checked += sizeof(uint8_t);
    }
    assert(bytes_checked == num);
    return 0;
}


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
    
    //printLog("getting tag for vaddr %p: [%x][%x]\n", vaddr,
    //        L1_INDX_BITS(vaddr), L2_INDX_BITS(vaddr));
    if(!l2)
    {

        printLog("TAGMAP ERROR for vaddr %p: l1 indx 0x%x is NULL\n", 
			vaddr, L1_INDX_BITS(vaddr));
        exit(1);
    }
    
    if(!l2[L2_INDX_BITS(vaddr)])
    {

        printLog("TAGMAP ERROR for vaddr %p: l2 indx 0x%x is NULL\n", 
			vaddr, L2_INDX_BITS(vaddr));
        exit(1);
    }

    return vaddr + l2[L2_INDX_BITS(vaddr)];
/*
err:
            FILE *in, *out;
            char ch;
            in = fopen("/proc/self/maps", "r");
            out = fopen("proc_maps", "w");
            if(in == NULL || out == NULL)
                printf("error opening file\n");
            while((ch = fgetc(in)) != EOF)
                fputc(ch, out);
            fclose(in);
            fclose(out);
            return KERNEL_TAINT_PAGE;
*/
}

//YMM register (256-bit) taint utility functions
uint128_t ymm_reg_get_taint(thread_ctx_t *thread_ctx, UINT32 reg)
{
   return (thread_ctx->vcpu.avx[reg][0] || thread_ctx->vcpu.avx[reg][1]);
}

uint128_t ymm_mem_get_taint(ADDRINT addr)
{
    ADDRINT tagaddr = get_tag_address(addr);
    return (*(uint128_t *)tagaddr || *(uint128_t *)(tagaddr + sizeof(uint128_t)));
}

