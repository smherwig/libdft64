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

/*
 * 06/03/2011:
 * 	the array structure that kept the per-thread contexts has been
 * 	replaced by TLS-like logic for performance and safety reasons;
 * 	Vasileios P. Kemerlis(vpk@cs.columbia.edu)
 */

#include <errno.h>
#include <string.h>
#include <unistd.h>
#include <iostream>
#include <fstream>
#include <fcntl.h>
#include <sys/types.h>
#include <sys/stat.h>

#include "libdft_api.h"
#include "libdft_instrument.h"
#include "syscall_desc.h"
#include "tagmap.h"
#include "branch_pred.h"


/* 
 * thread context pointer (TLS emulation); we
 * spill a register for emulating TLS-like storage.
 * Specifically, thread_ctx_ptr shall hold the
 * address of a per-thread context structure
 */
REG thread_ctx_ptr;

/* syscall descriptors */
extern syscall_desc_t syscall_desc[SYSCALL_MAX];

/* ins descriptors */
ins_desc_t ins_desc[XED_ICLASS_LAST];


/*
 * thread start callback (analysis function)
 *
 * allocate space for the syscall context and VCPUs
 * (i.e., thread context), and set the TLS-like pointer
 * (i.e., thread_ctx_ptr) accordingly
 *
 * @tid:	thread id
 * @ctx:	CPU context
 * @flags:	OS specific flags for the new thread
 * @v:		callback value
 */
static void
thread_alloc(THREADID tid, CONTEXT *ctx, INT32 flags, VOID *v)
{
	/* thread context pointer (ptr) */
	thread_ctx_t *tctx = NULL;

	/* allocate space for the thread context; optimized branch */
	if (unlikely((tctx = (thread_ctx_t *)calloc(1,
					sizeof(thread_ctx_t))) == NULL)) {
		/* error message */
		LOG(string(__func__) + ": thread_ctx_t allocation failed (" +
				string(strerror(errno)) + ")\n");
		
		/* die */
		libdft_die();
	}

	/* save the address of the per-thread context to the spilled register */
	PIN_SetContextReg(ctx, thread_ctx_ptr, (ADDRINT)tctx);
}

/*
 * thread finish callback (analysis function)
 *
 * free the space for the syscall context and VCPUs
 *
 * @tid:	thread id
 * @ctx:	CPU context
 * @code:	OS specific termination code for the thread
 * @v:		callback value
 */
static void
thread_free(THREADID tid, const CONTEXT *ctx, INT32 code, VOID *v)
{
	/* get the thread context */
	thread_ctx_t *tctx = (thread_ctx_t *)
		PIN_GetContextReg(ctx, thread_ctx_ptr);

	/* free the allocated space */
	free(tctx);
}


/* 
 * syscall enter notification (analysis function)
 *
 * save the system call context and invoke the pre-syscall callback
 * function (if registered)
 *
 * @tid:	thread id
 * @ctx:	CPU context
 * @std:	syscall standard (e.g., Linux IA-32, IA-64, etc)
 * @v:		callback value
 */
static void
sysenter_save(THREADID tid, CONTEXT *ctx, SYSCALL_STANDARD std, VOID *v)
{
	/* get the thread context */
	thread_ctx_t *thread_ctx = (thread_ctx_t *)
		PIN_GetContextReg(ctx, thread_ctx_ptr);

	/* get the syscall number */
	ADDRINT syscall_nr = PIN_GetSyscallNumber(ctx, std);

	/* unknown syscall; optimized branch */
	if (unlikely(syscall_nr >= SYSCALL_MAX)) {
		LOG(string(__func__) + ": unknown syscall (num=" +
				decstr(syscall_nr) + ")\n");
		/* syscall number is set to -1; hint for the sysexit_save() */
		thread_ctx->syscall_ctx.nr = -1;
		/* no context save and no pre-syscall callback invocation */
		return;
	}
#ifdef SYSCALL_DEBUG
    printLog("Sysenter save for syscall num %lu\n", syscall_nr);
#endif    
    /* pass the system call number to sysexit_save() */
	thread_ctx->syscall_ctx.nr = syscall_nr;

	/*
	 * check if we need to save the arguments for that syscall
	 *
	 * we save only when we have a callback registered or the syscall
	 * returns a value in the arguments
	 */
	if (syscall_desc[syscall_nr].save_args |
		syscall_desc[syscall_nr].retval_args) {
		/*
		 * dump only the appropriate number of arguments
		 * or yet another lame way to avoid a loop (vpk)
		 */
		switch (syscall_desc[syscall_nr].nargs) {
			/* 6 */
			case SYSCALL_ARG5 + 1:
				thread_ctx->syscall_ctx.arg[SYSCALL_ARG5] =
					PIN_GetSyscallArgument(ctx,
								std,
								SYSCALL_ARG5);
			/* 5 */
			case SYSCALL_ARG4 + 1:
				thread_ctx->syscall_ctx.arg[SYSCALL_ARG4] =
					PIN_GetSyscallArgument(ctx,
								std,
								SYSCALL_ARG4);
			/* 4 */
			case SYSCALL_ARG3 + 1:
				thread_ctx->syscall_ctx.arg[SYSCALL_ARG3] =
					PIN_GetSyscallArgument(ctx,
								std,
								SYSCALL_ARG3);
			/* 3 */
			case SYSCALL_ARG2 + 1:
				thread_ctx->syscall_ctx.arg[SYSCALL_ARG2] =
					PIN_GetSyscallArgument(ctx,
								std,
								SYSCALL_ARG2);
			/* 2 */
			case SYSCALL_ARG1 + 1:
				thread_ctx->syscall_ctx.arg[SYSCALL_ARG1] =
					PIN_GetSyscallArgument(ctx,
								std,
								SYSCALL_ARG1);
			/* 1 */
			case SYSCALL_ARG0 + 1:
				thread_ctx->syscall_ctx.arg[SYSCALL_ARG0] =
					PIN_GetSyscallArgument(ctx,
								std,
								SYSCALL_ARG0);
			/* default */
			default:
				/* nothing to do */
				break;
		}

		/* 
		 * dump the architectural state of the processor;
		 * saved as "auxiliary" data
		 */
		thread_ctx->syscall_ctx.aux = ctx;

		/* call the pre-syscall callback (if any) */
		if (syscall_desc[syscall_nr].pre != NULL)
			syscall_desc[syscall_nr].pre(&thread_ctx->syscall_ctx, ctx, std);
	}
}

/* 
 * syscall exit notification (analysis function)
 *
 * save the system call context and invoke the post-syscall callback
 * function (if registered)
 *
 * NOTE: it performs tag cleanup for the syscalls that have side-effects in
 * their arguments
 *
 * @tid:	thread id
 * @ctx:	CPU context
 * @std:	syscall standard (e.g., Linux IA-32, IA-64, etc)
 * @v:		callback value
 */
static void
sysexit_save(THREADID tid, CONTEXT *ctx, SYSCALL_STANDARD std, VOID *v)
{
	/* iterator */
	size_t i;

	/* get the thread context */
	thread_ctx_t *thread_ctx = (thread_ctx_t *)
		PIN_GetContextReg(ctx, thread_ctx_ptr);

	/* get the syscall number */
	ADDRINT syscall_nr = thread_ctx->syscall_ctx.nr;
	
#ifdef SYSCALL_DEBUG
    printLog("Start of Sysexit save for syscall %lu\n", syscall_nr);
#endif

    /* unknown syscall; optimized branch */
	if (unlikely(syscall_nr > SYSCALL_MAX)) {
		LOG(string(__func__) + ": unknown syscall (num=" +
				decstr(syscall_nr) + ")\n");
		/* no context save and no pre-syscall callback invocation */
		return;
	}
	
	/*
	 * check if we need to save the arguments for that syscall
	 *
	 * we save only when we have a callback registered or the syscall
	 * returns a value in the arguments
	 */
	if (syscall_desc[syscall_nr].save_args |
			syscall_desc[syscall_nr].retval_args) {
		/* dump only the appropriate number of arguments */
		thread_ctx->syscall_ctx.ret = PIN_GetSyscallReturn(ctx, std);

		/* 
		 * dump the architectural state of the processor;
		 * saved as "auxiliary" data
		 */
		thread_ctx->syscall_ctx.aux = ctx;

		/* thread_ctx->syscall_ctx.errno =
			PIN_GetSyscallErrno(ctx, std); */
	
		/* call the post-syscall callback (if any) */
		if (syscall_desc[syscall_nr].post != NULL)
        {
			syscall_desc[syscall_nr].post(&thread_ctx->syscall_ctx, ctx, std);
        }
		else {
			/* default post-syscall handling */

			/* 
			 * the syscall failed; typically 0 and positive
			 * return values indicate success
			 */
			if (thread_ctx->syscall_ctx.ret < 0)
				/* no need to do anything */
				return;

			/* traverse the arguments map */
			for (i = 0; i < syscall_desc[syscall_nr].nargs; i++)
				/* analyze each argument; optimized branch */
			if (unlikely(syscall_desc[syscall_nr].map_args[i] > 0)) 
				/* sanity check -- probably non needed */
				if (likely(
				(void *)thread_ctx->syscall_ctx.arg[i] != NULL))
				/* 
				 * argument i is changed by the system call;
				 * the length of the change is given by
				 * map_args[i]
				 */
				tagmap_clrn(thread_ctx->syscall_ctx.arg[i],
					syscall_desc[syscall_nr].map_args[i]);
		}
#ifdef SYSCALL_DEBUG
    printLog("End of sysexit save for syscall %u\n", syscall_nr);
#endif
	}
}
/*
 * trace inspection (instrumentation function)
 *
 * traverse the basic blocks (BBLs) on the trace and
 * inspect every instruction for instrumenting it
 * accordingly
 *
 * @trace:      instructions trace; given by PIN
 * @v:		callback value
 */
#ifdef TRACE_INSTRUMENT
static void
trace_inspect(TRACE trace, VOID *v)
{
    /* iterators */
	BBL bbl;
	INS ins;
	xed_iclass_enum_t ins_indx;
    bbl=TRACE_BblHead(trace);
    ins = BBL_InsHead(bbl);

    //If don't need to be tracking taint, just return
    if(!instrumentFlag){
        return;
    }

	/* traverse all the BBLs in the trace */
	for (bbl = TRACE_BblHead(trace); BBL_Valid(bbl); bbl = BBL_Next(bbl)) 
    {
		/* traverse all the instructions in the BBL */
#ifdef INS_DEBUG
        printLog("New BBL\n");
#endif
        
		for (ins = BBL_InsHead(bbl);
				INS_Valid(ins);
				ins = INS_Next(ins)) 
        {
    	        /*
				 * use XED to decode the instruction and
				 * extract its opcode
				 */
				ins_indx = (xed_iclass_enum_t)INS_Opcode(ins);

				/* 
				 * invoke the pre-ins instrumentation callback
				 */
				if (ins_desc[ins_indx].pre != NULL)
					ins_desc[ins_indx].pre(ins);

				/* 
				 * analyze the instruction (default handler)
				 */
				if (ins_desc[ins_indx].dflact == INSDFL_ENABLE)
					ins_inspect(ins);

				/* 
				 * invoke the post-ins instrumentation callback
				 */
				if (ins_desc[ins_indx].post != NULL)
					ins_desc[ins_indx].post(ins);
                
		}
	}
}
#endif

#ifdef RTN_INSTRUMENT
/*
 * rtn inspection (instrumentation function)
 *
 *
 * @rtn      instructions trace; given by PIN
 * @v:		callback value
 */
static void
rtn_inspect(RTN rtn, VOID *v)
{
    RTN_Open(rtn);


	xed_iclass_enum_t ins_indx;
	
	for (INS ins = RTN_InsHead(rtn); INS_Valid(ins); ins = INS_Next(ins)) {

    	        /*
				 * use XED to decode the instruction and
				 * extract its opcode
				 */
				ins_indx = (xed_iclass_enum_t)INS_Opcode(ins);

				/* 
				 * invoke the pre-ins instrumentation callback
				 */
				if (ins_desc[ins_indx].pre != NULL)
					ins_desc[ins_indx].pre(ins);

				/* 
				 * analyze the instruction (default handler)
				 */
				if (ins_desc[ins_indx].dflact == INSDFL_ENABLE)
					ins_inspect(ins);

				/* 
				 * invoke the post-ins instrumentation callback
				 */
				if (ins_desc[ins_indx].post != NULL)
					ins_desc[ins_indx].post(ins);
	}
    RTN_Close(rtn);
}
#endif
/*
 * initialize thread contexts
 *
 * spill a tool register for the thread contexts
 * and register a thread start callback
 *
 * returns: 0 on success, 1 on error
 */
static inline int
thread_ctx_init(void)
{
	/* claim a tool register; optimized branch */
	if (unlikely(
		(thread_ctx_ptr = PIN_ClaimToolRegister()) == REG_INVALID())) {
		/* error message */
		LOG(string(__func__) + ": register claim failed\n");

		/* failed */
		return 1;
	}

	/* 
	 * thread start/stop hooks;
	 * keep track of the threads and allocate/free space for the
	 * per-thread logistics (i.e., syscall context, VCPU, etc)
	 */
	PIN_AddThreadStartFunction(thread_alloc, NULL);
	PIN_AddThreadFiniFunction(thread_free,	NULL);

	/* success */
	return 0;
}

/*
 * global handler for internal errors (i.e., errors from libdft)
 *
 * handle memory protection (e.g., R/W/X access to null_seg)
 * 	-- or --
 * for unknown reasons, when an analysis function is executed,
 * the EFLAGS.AC bit (i.e., bit 18) is asserted, thus leading
 * into a runtime exception whenever an unaligned read/write
 * is performed from libdft. This callback can be registered
 * with PIN_AddInternalExceptionHandler() so as to trap the
 * generated signal and remediate
 *
 * @tid:		thread id		
 * @pExceptInfo:	exception descriptor
 * @pPhysCtxt:		physical processor state
 * @v:			callback value
 */
static EXCEPT_HANDLING_RESULT
excpt_hdlr(THREADID tid, EXCEPTION_INFO *pExceptInfo,
		PHYSICAL_CONTEXT *pPhysCtxt, VOID *v)
{
	/* memory violation address (fault) */
	ADDRINT vaddr = 0x0;

	/* unaligned memory accesses */
	if (PIN_GetExceptionCode(pExceptInfo) ==
			EXCEPTCODE_ACCESS_MISALIGNED) {
		/* clear EFLAGS.AC */
		PIN_SetPhysicalContextReg(pPhysCtxt, REG_EFLAGS,
			CLEAR_EFLAGS_AC(PIN_GetPhysicalContextReg(pPhysCtxt,
					REG_EFLAGS)));
		
		/* the exception is handled gracefully; commence execution */
		return EHR_HANDLED;
	}
	/* memory protection */
	else if (PIN_GetExceptionCode(pExceptInfo) ==
			EXCEPTCODE_ACCESS_DENIED) {
		
		/* get the address of the memory violation */	
		PIN_GetFaultyAccessAddress(pExceptInfo, &vaddr);
		
		/* sanity check */
        tagmap_l2_t l2 = (tagmap_l2_t)TAGMAP_L1[L1_INDX_BITS(vaddr)];
		if (l2  == NULL || l2[L2_INDX_BITS(vaddr)] == 0)
        {
			/* error message */
			LOG(string(__func__) + ": invalid access -- " +
					"memory protection triggered\n");

			/* terminate the application */
			PIN_ExitProcess(-1);
		}
	}
	
	/* unknown exception; pass to the application */
	return EHR_UNHANDLED;
}



/*
 * initialization of the core tagging engine;
 * it must be called before using everything else
 *
 * returns: 0 on success, 1 on error
 */
int
libdft_init(void)
{
    /* initialize thread contexts; optimized branch */
	if (unlikely(thread_ctx_init()))
		/* thread contexts failed */
		return 1;

	/* initialize the tagmap; optimized branch */
	if (unlikely(tagmap_alloc()))
		/* tagmap initialization failed */
		return 1;
	
	/*
	 * syscall hooks; store the context of every syscall
	 * and invoke registered callbacks (if any)
	 */

	/* register sysenter_save() to be called before every syscall */
	PIN_AddSyscallEntryFunction(sysenter_save, NULL);
	
	/* register sysexit_save() to be called after every syscall */
	PIN_AddSyscallExitFunction(sysexit_save, NULL);
#ifdef SYSCALL_DEBUG
    printLog("registered sycall funs\n");
#endif    
	/* initialize the ins descriptors */
	(void)memset(ins_desc, 0, sizeof(ins_desc));

	/* register trace_ins() to be called for every trace */
#ifdef TRACE_INSTRUMENT
	TRACE_AddInstrumentFunction(trace_inspect, NULL);
#endif    
#ifdef INS_INSTRUMENT
    INS_AddInstrumentFunction(ins_inspect, NULL);
#endif
	/* 
	 * register excpt_hdlr() to be called for handling internal
	 * (i.e., libdft or tool-related) exceptions
	 */
	PIN_AddInternalExceptionHandler(excpt_hdlr, NULL);
	
	/* success */
	return 0;
}

/*
 * stop the execution of the application inside the
 * tag-aware VM; the execution of the application
 * is not interrupted
 */
void
libdft_die(void)
{
       /*
        * detach Pin from the application;
        * the application will continue to execute natively
        */
       PIN_Detach();
}

/*
 * add a new pre-ins callback into an instruction descriptor
 *
 * @desc:	the ins descriptor
 * @pre:	function pointer to the pre-ins handler
 *
 * returns:	0 on success, 1 on error
 */
int
ins_set_pre(ins_desc_t *desc, void (* pre)(INS))
{
	/* sanity checks; optimized branch */
	if (unlikely((desc == NULL) | (pre == NULL)))
		/* return with failure */
		return 1;

	/* update the pre-ins callback */
	desc->pre = pre;

	/* success */
	return 0;
}

/*
 * add a new post-ins callback into an instruction descriptor
 *
 * @desc:	the ins descriptor
 * @post:	function pointer to the post-ins handler
 *
 * returns:	0 on success, 1 on error
 */
int
ins_set_post(ins_desc_t *desc, void (* post)(INS))
{
	/* sanity checks; optimized branch */
	if (unlikely((desc == NULL) | (post == NULL)))
		/* return with failure */
		return 1;

	/* update the post-ins callback */
	desc->post = post;

	/* success */
	return 0;
}

/*
 * remove the pre-ins callback from an instruction descriptor
 *
 * @desc:	the ins descriptor
 *
 * returns:     0 on success, 1 on error
 */
int
ins_clr_pre(ins_desc_t *desc)
{
	/* sanity check; optimized branch */
	if (unlikely(desc == NULL))
		/* return with failure */
		return 1;

	/* clear the pre-ins callback */
	desc->pre = NULL;

        /* return with success */
        return 0;
}

/*
 * remove the post-ins callback from an instruction descriptor
 *
 * @desc:	the ins descriptor
 *
 * returns:	0 on success, 1 on error
 */
int
ins_clr_post(ins_desc_t *desc)
{
	/* sanity check; optimized branch */
	if (unlikely(desc == NULL))
		/* return with failure */
		return 1;

	/* clear the post-ins callback */
	desc->post = NULL;

        /* return with success */
        return 0;
}

/*
 * set (enable/disable) the default action in an instruction descriptor
 *
 * @desc:       the ins descriptor
 *
 * returns:     0 on success, 1 on error
 */
int
ins_set_dflact(ins_desc_t *desc, size_t action)
{
	/* sanity checks */
	
	/* optimized branch */
	if (unlikely(desc == NULL))
		/* return with failure */
		return 1;

	switch (action) {
		/* valid actions */
		case INSDFL_ENABLE:
		case INSDFL_DISABLE:
			break;
		/* default handler */
		default:
			/* return with failure */
			return 1;
	}

	/* set the default action */
	desc->dflact = action;

        /* return with success */
        return 0;
}


void printLog(const char *fmt, ...)
{
#ifdef DEBUG
    
    //int log_fd = open("libdft.log", O_RDWR|O_APPEND);    
    FILE* log_file = fopen("libdft.log", "a");
    chmod("libdft.log", 0666);

  if(log_file)
  {
   va_list args;
   va_start(args, fmt);
   vfprintf(log_file, fmt, args);
   va_end(args);
   fclose(log_file);
  }
#endif
}

int page_is_tainted(ADDRINT taint_page_addr)
{
#ifdef EXTRA_DEBUG
    printLog("Checking taint page 0x%lx for taint\n", taint_page_addr);
#endif
    for(ADDRINT chunk = taint_page_addr; chunk < taint_page_addr + PAGE_SIZE; chunk += sizeof(ADDRINT))
    {
        if(*(ADDRINT*)chunk)
            return 1;
    }
    return 0;
}

ADDRINT tainted_bytes_on_page(ADDRINT addr)
{
#ifdef EXTRA_DEBUG_MEMTRACK
    printLog("Checking if %d bytes are tainted at 0x%lx\n", num, addr);
#endif
    ADDRINT start;
    int bytes_tainted = 0;
    int last = 0;
    for(start = addr; start < addr + PAGE_SIZE; start++){
        if(tagmap_getb(start)){
            if(!last){
                printLog("0x%lx - ", start);
                last = 1;
            }
            bytes_tainted++;
        }
        else{
            if(last){
                printLog("0x%lx\n", start);
                last = 0;
            }
        }
    }
    if(last)
        printLog("0x%lx\n", start);
    return bytes_tainted;
}

/* Debug function: print tainted pages in stab */
void printPageTaints(){
#ifdef DEBUG
    int num_pages_allocated = 0,  num_pages_tainted = 0, num_l2s = 0;
    tagmap_l2_t l2;
    printLog("\nPage taints for process %d\n", PIN_GetPid());
    ADDRINT vaddr, tag_addr;
    for(UINT i = 0; i < NUM_L1_ENTRIES; i++)
    {
        l2 = (tagmap_l2_t)TAGMAP_L1[i];
        if(l2)
        {
            printLog("L1 indx %x has L2 allocated\n", i);
            num_l2s++;

            for(UINT j = 0; j < NUM_L2_ENTRIES; j++)
            {
                if(l2[j])
                {
                    //printLog("L2 indx %x has offset\n", j);
                    num_pages_allocated++;
                    vaddr = ((ADDRINT)i << (TOTAL_ADDR_BITS - NUM_L1_BITS)) + 
                            ((ADDRINT)j << PAGE_SHIFT);
                    tag_addr = vaddr + l2[j];
                    if( ((vaddr + l2[j]) != (ADDRINT)zero_seg) &&
                            page_is_tainted(vaddr + l2[j]))
                    {
                        printLog("0x%lx is tainted\n", vaddr); 
                        num_pages_tainted++;
                    }

                }
            
            }
        }
    }        
    printLog("Num l2 arrays allocated: %d \nNum tag pages allocated: %d\n"
            "Num tag pages tainted: %d\n", 
            num_l2s, num_pages_allocated, num_pages_tainted);
    
#endif
}

/* Debug function: print tainted pages, and tainted bytes within each page
 * in stab */
void printPageAndByteTaints(){
#ifdef DEBUG
    int num_pages_allocated = 0,  num_pages_tainted = 0;
    tagmap_l2_t l2;
    printLog("\nTainted Pages and bytes for process %d\n", PIN_GetPid());
    ADDRINT vaddr;
    for(UINT i = 0; i < NUM_L1_ENTRIES; i++)
    {
        l2 = (tagmap_l2_t)TAGMAP_L1[i];
        if(l2)
        {
            for(UINT j = 0; j < NUM_L2_ENTRIES; j++)
            {
                if(l2[j])
                {
                    num_pages_allocated++;
                    vaddr = ((ADDRINT)i << (TOTAL_ADDR_BITS - NUM_L1_BITS)) + 
                            ((ADDRINT)j << PAGE_SHIFT);
                    if( ((vaddr + l2[j]) != (ADDRINT)zero_seg) && 
                            page_is_tainted(vaddr + l2[j]))
                    {
                        printLog("0x%lx is tainted:\n", vaddr);
                        int tainted_bytes = tainted_bytes_on_page(vaddr);
                        printLog("0x%lx is tainted with %d bytes\n", vaddr, tainted_bytes); 
                        //printLog("0x%lx is tainted with %d bytes\n", vaddr, tainted_bytes_on_page(vaddr)); 
                        num_pages_tainted++;
                    }

                }
            
            }
        }
    }        
    printLog("Num tag pages allocated: %d\n"
            "Num tag pages tainted: %d\n", 
            num_pages_allocated, num_pages_tainted);
    
#endif
}

void printRegTaints(const CONTEXT* ctx)
{
    thread_ctx_t *thread_ctx = (thread_ctx_t *)                                                                
                PIN_GetContextReg(ctx, thread_ctx_ptr);
    printLog("Register taints:\n");
    for(int i = 0; i <= GPR_NUM; i++)
        printLog("%d: %u\n", i, thread_ctx->vcpu.gpr[i]);
    printLog("\n");
}

/* Allocates and fills an array, *pages, of all tainted pages to 
 * export to picojump. Returns the number tainted pages
 */
int getTaintedPagesBuf(ADDRINT **taintedPages){
    int num_pages_tainted = 0, capacity = INIT_BUF_CAP;
    tagmap_l2_t l2;
    ADDRINT vaddr, tag_addr;
    //FILE *f = fopen(TAINT_FILE, "wb");
    *taintedPages = (ADDRINT *)calloc(capacity, sizeof(vaddr));
    ADDRINT *pages = *taintedPages;
    for(UINT i = 0; i < NUM_L1_ENTRIES; i++)
    {
        l2 = (tagmap_l2_t)TAGMAP_L1[i];
        if(l2)
        {
            for(UINT j = 0; j < NUM_L2_ENTRIES; j++)
            {
                if(l2[j])
                {
                    vaddr = ((ADDRINT)i << (TOTAL_ADDR_BITS - NUM_L1_BITS)) + 
                            ((ADDRINT)j << PAGE_SHIFT);
                    tag_addr = vaddr + l2[j];
                    if( ((vaddr + l2[j]) != (ADDRINT)zero_seg) &&
                            page_is_tainted(vaddr + l2[j]))
                    {
                        //fwrite(&vaddr, sizeof(vaddr), 1, f);
                        if (num_pages_tainted == capacity - 1){
                           //resize
                           capacity *= 2;
                           *taintedPages = (ADDRINT *)realloc(
                                   *taintedPages, capacity * sizeof(ADDRINT));
                        }
                        pages[num_pages_tainted++] = vaddr;
                    }
                }
            }
        }
    }
    //fclose(f);
    return num_pages_tainted;
}

void freeTaintedPagesBuf(ADDRINT *taintedPages){
    free(taintedPages);
}


string uint128_hex_string(uint128_t *num)
{
    char buf[36] = {0};
    snprintf(buf, 35, "0x%lx %lx", *(UINT64 *)num, 
            *(((UINT64 *)num) + 1));
    return *(new string(buf));
}

string uint256_hex_string(uint256_t *num)
{
    char buf[70] = {0};
    snprintf(buf, 69, "0x%lx %lx %lx %lx", *((UINT64 *)num), 
            *(((UINT64 *)num) + 1), *(((UINT64 *)num) + 2),
            *(((UINT64 *)num) + 3)); 
    return *(new string(buf));
}

string uint512_hex_string(uint512_t *num)
{
    char buf[138] = {0};
    snprintf(buf, 137, "0x%lx %lx %lx %lx %lx %lx %lx %lx", *((UINT64 *)num), 
            *(((UINT64 *)num) + 1), *(((UINT64 *)num) + 2),
            *(((UINT64 *)num) + 3), *(((UINT64 *)num) + 4), 
            *(((UINT64 *)num) + 5), *(((UINT64 *)num) + 6), 
            *(((UINT64 *)num) + 7)); 
    return *(new string(buf));
}
