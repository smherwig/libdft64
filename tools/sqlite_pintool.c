/*-
 * Copyright (c) 2011, 2012, 2013, Columbia University
 * All rights reserved.
 *
 * This software was developed by Vasileios P. Kemerlis <vpk@cs.columbia.edu>
 * at Columbia University, New York, NY, USA, in October 2011.
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
 * TODO:
 * 	- add support for file descriptor duplication via fcntl(2)
 * 	- add support for non PF_INET* sockets
 * 	- add support for recvmmsg(2)
 */

#include <errno.h>
#include <sys/socket.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <set>
#include <iostream>
#include <fstream>

#include "branch_pred.h"
#include "libdft_api.h"
#include "libdft_instrument.h"
#include "syscall_desc.h"
#include "tagmap.h"
#include "pin.H"

#define WORD_LEN	4	/* size in bytes of a word value */
#define SYS_SOCKET	1	/* socket(2) demux index for socketcall */

/* default path for the log file (audit) */
#define LOGFILE_DFL	"mem_trace.log"

/* default suffixes for dynamic shared libraries */
#define DLIB_SUFF	".so"
#define DLIB_SUFF_ALT	".so."

#define HANDSHAKE_FUNCTION "SSL_do_handshake"

/* thread context */
extern REG thread_ctx_ptr;

/* ins descriptors */
extern ins_desc_t ins_desc[XED_ICLASS_LAST];

/* syscall descriptors */
extern syscall_desc_t syscall_desc[SYSCALL_MAX];

/* set of interesting descriptors (sockets) */
static set<int> fdset;

/* log file path (auditing) */
static KNOB<string> logpath(KNOB_MODE_WRITEONCE, "pintool", "l",
		LOGFILE_DFL, "");

int instrumentFlag = 0;
int prePropFlag = 0;
int postPropFlag = 1;

PIN_LOCK pin_lock;
#if 1
/*
 * read(2) handler (taint-source)
 */
static void
post_read_hook(syscall_ctx_t *ctx, CONTEXT *pin_ctx, SYSCALL_STANDARD std)
{

    /* read() was not successful; optimized branch */
    if (unlikely((long)ctx->ret <= 0))
            return;
    /* taint-source */
	if (fdset.find(ctx->arg[SYSCALL_ARG0]) != fdset.end()){
        	/* set the tag markings */
	        tagmap_setn(ctx->arg[SYSCALL_ARG1], (size_t)ctx->ret, TAG_ALL8);
#ifdef DEBUG
            printLog("tainted %d bytes at address 0x%lx from read\n", (size_t)ctx->ret, ctx->arg[SYSCALL_ARG1]);
            //printPageTaints();
#endif
            instrumentFlag = 1;
            postPropFlag = 1;
            //CODECACHE_FlushCache();
#ifdef DEBUG
            //printf("set instrument flag and cleared cache\n");
#endif
    }

	else
        	/* clear the tag markings */
	        tagmap_clrn(ctx->arg[SYSCALL_ARG1], (size_t)ctx->ret);
}
#endif
#if 0
static void tool_post_mmap_hook(syscall_ctx_t *ctx, CONTEXT *pin_ctx, SYSCALL_STANDARD std)
{
    post_mmap_hook(ctx, pin_ctx, std);

   printLog("mmaped at 0x%lx  (0:%lx 1:%lu 2:%lu 3:%lu 4:%ld 5:%lu)\n", 
            ctx->ret, ctx->arg[SYSCALL_ARG0], ctx->arg[SYSCALL_ARG1],
            ctx->arg[SYSCALL_ARG2], ctx->arg[SYSCALL_ARG3],  
            ctx->arg[SYSCALL_ARG4], ctx->arg[SYSCALL_ARG5]);
            
    // taint-source 
	if (fdset.find(ctx->arg[SYSCALL_ARG4]) != fdset.end()){
        	// set the tag markings 
	        tagmap_setn(ctx->ret, ctx->arg[SYSCALL_ARG1], TAG_ALL8);
            printLog("tainted %d bytes at address %x from mmap\n", ctx->arg[SYSCALL_ARG1], (size_t)ctx->ret);
            printPageTaints();
    }
}
#endif

/*
 * readv(2) handler (taint-source)
 */
static void
post_readv_hook(syscall_ctx_t *ctx, CONTEXT *pin_ctx, SYSCALL_STANDARD std)
{
	/* iterators */
	int i;
	struct iovec *iov;
	set<int>::iterator it;

	/* bytes copied in a iovec structure */
	size_t iov_tot;

	/* total bytes copied */
	size_t tot = (size_t)ctx->ret;

	/* readv() was not successful; optimized branch */
	if (unlikely((long)ctx->ret <= 0))
		return;
	
	/* get the descriptor */
	it = fdset.find((int)ctx->arg[SYSCALL_ARG0]);

	/* iterate the iovec structures */
	for (i = 0; i < (int)ctx->arg[SYSCALL_ARG2] && tot > 0; i++) {
		/* get an iovec  */
		iov = ((struct iovec *)ctx->arg[SYSCALL_ARG1]) + i;
		
		/* get the length of the iovec */
		iov_tot = (tot >= (size_t)iov->iov_len) ?
			(size_t)iov->iov_len : tot;
	
		/* taint interesting data and zero everything else */	
		if (it != fdset.end())
                	/* set the tag markings */
                	tagmap_setn((size_t)iov->iov_base, iov_tot, TAG_ALL8);
		else
                	/* clear the tag markings */
                	tagmap_clrn((size_t)iov->iov_base, iov_tot);

                /* housekeeping */
                tot -= iov_tot;
        }
}

/*
 * auxiliary (helper) function
 *
 * duplicated descriptors are added into
 * the monitored set
 */
static void
post_dup_hook(syscall_ctx_t *ctx, CONTEXT *pin_ctx, SYSCALL_STANDARD std)
{
	/* not successful; optimized branch */
	if (unlikely((long)ctx->ret < 0))
		return;
	
	/*
	 * if the old descriptor argument is
	 * interesting, the returned handle is
	 * also interesting
	 */
	if (likely(fdset.find((int)ctx->arg[SYSCALL_ARG0]) != fdset.end()))
		fdset.insert((int)ctx->ret);
}

/*
 * auxiliary (helper) function
 *
 * whenever close(2) is invoked, check
 * the descriptor and remove if it was
 * inside the monitored set of descriptors
 */
static void
post_close_hook(syscall_ctx_t *ctx, CONTEXT *pin_ctx, SYSCALL_STANDARD std)
{
	/* iterator */
	set<int>::iterator it;

	/* not successful; optimized branch */
	if (unlikely((long)ctx->ret < 0))
		return;
	
	/*
	 * if the descriptor (argument) is
	 * interesting, remove it from the
	 * monitored set
	 */
	it = fdset.find((int)ctx->arg[SYSCALL_ARG0]);
	if (likely(it != fdset.end()))
		fdset.erase(it);
    
//    printLog("Post close call on fd %d in pid %d\n", ctx->arg[SYSCALL_ARG0], PIN_GetPid()); 
//    printPageTaints();
}

/*
 * auxiliary (helper) function
 *
 * whenever open(2)/creat(2) is invoked,
 * add the descriptor inside the monitored
 * set of descriptors
 *
 * NOTE: it does not track dynamic shared
 * libraries
 */
static void
post_open_hook(syscall_ctx_t *ctx, CONTEXT *pin_ctx, SYSCALL_STANDARD std)
{
	
	set<int>::iterator it;

    /* not successful; optimized branch */
	if (unlikely((long)ctx->ret < 0))
		return;
	
    /*check if the file being opened is the private key*/
    ADDRINT fileArg = PIN_GetSyscallArgument(pin_ctx, std, 0);
    ADDRINT ret =  PIN_GetSyscallReturn(pin_ctx, std);
    int fnlen = strlen((char*)fileArg);
    printf("opening %s\n", (char *)fileArg);
    if(strncmp("data_files/m1.csv", (char*)(fileArg), fnlen) == 0){
#ifdef DEBUG
        printLog("Added %d to fdset\n", ret);
#endif
        fdset.insert(ret);
    }
}


// This function is called when the application exits
VOID Fini(INT32 code, VOID *v)
{
    PIN_GetLock(&pin_lock, PIN_GetPid());
    printLog("process %d finished\n", PIN_GetPid());
    printPageTaints();
    printPageAndByteTaints();
    printLog("space used by pin: %uB (%umb)\n", 
            PIN_MemoryAllocatedForPin(), (PIN_MemoryAllocatedForPin() >> 20));
    PIN_ReleaseLock(&pin_lock);
}

VOID BeforeFork(THREADID threadid, const CONTEXT *ctxt, VOID *arg)
{
    PIN_GetLock(&pin_lock, threadid + 1);
    printLog("Before fork\n");
    //printPageTaints();
    printRegTaints(ctxt);
    PIN_ReleaseLock(&pin_lock);
}

VOID AfterForkInChild(THREADID threadid, const CONTEXT* ctxt, VOID * arg)
{
    PIN_GetLock(&pin_lock, threadid + 1);
    printLog("after fork in child process %d\n", PIN_GetPid());
    //printPageTaints();
    printRegTaints(ctxt);
    PIN_ReleaseLock(&pin_lock);
}


/* 
VOID HandshakeBefore(CHAR * name, ADDRINT *ssl_struct)
{
    printLog("DECLASSIFY %s (ssl struct at %p)\n", name, ssl_struct);
}

VOID HandshakeAfter(ADDRINT ret)
{
    printLog("DECLASSIFY return value %ld\n", ret);
}
VOID InstrumentImage(IMG img, VOID *v)
{
    // Instrument the malloc() and free() functions.  Print the input argument
    // of each malloc() or free(), and the return value of malloc().
    //
    cout << "opened image " << IMG_Name(img) << endl;
    RTN handshakeRtn = RTN_FindByName(img, HANDSHAKE_FUNCTION);
    if (RTN_Valid(handshakeRtn))
    {
        cout << "found " << HANDSHAKE_FUNCTION << endl;
        RTN_Open(handshakeRtn);

        // Instrument malloc() to print the input argument value and the return value.
        RTN_InsertCall(handshakeRtn, IPOINT_BEFORE, (AFUNPTR)HandshakeBefore,
                       IARG_ADDRINT, HANDSHAKE_FUNCTION,
                       IARG_FUNCARG_ENTRYPOINT_REFERENCE, 0,
                       IARG_END);
        RTN_InsertCall(handshakeRtn, IPOINT_AFTER, (AFUNPTR)HandshakeAfter,
                       IARG_FUNCRET_EXITPOINT_VALUE, IARG_END);

        RTN_Close(handshakeRtn);
    }
}
*/

/* 
 * DTA
 *
 * used for demonstrating how to implement
 * a practical dynamic taint analysis (DTA)
 * tool using libdft
 */
int
main(int argc, char **argv)
{
	/* initialize symbol processing */
	PIN_InitSymbols();
    PIN_InitLock(&pin_lock);	
	/* initialize Pin; optimized branch */
	if (unlikely(PIN_Init(argc, argv)))
		/* Pin initialization failed */
		goto err;

	/* initialize the core tagging engine */
	if (unlikely(libdft_init() != 0))
		/* failed */
		goto err;
	/* read(2) */

	(void)syscall_set_post(&syscall_desc[__NR_read], post_read_hook);

	/* readv(2) */
	(void)syscall_set_post(&syscall_desc[__NR_readv], post_readv_hook);

	/* dup(2), dup2(2) */
	(void)syscall_set_post(&syscall_desc[__NR_dup], post_dup_hook);
	(void)syscall_set_post(&syscall_desc[__NR_dup2], post_dup_hook);

	/* close(2) */
	(void)syscall_set_post(&syscall_desc[__NR_close], post_close_hook);
	
	/* open(2), creat(2) */
	(void)syscall_set_post(&syscall_desc[__NR_open],
			post_open_hook);
	(void)syscall_set_post(&syscall_desc[__NR_creat],
			post_open_hook);


    //declassification
//    IMG_AddInstrumentFunction(InstrumentImage, 0);

#ifdef DEBUG
    PIN_AddForkFunction(FPOINT_BEFORE, BeforeFork, 0);
    PIN_AddForkFunction(FPOINT_AFTER_IN_CHILD, AfterForkInChild, 0);
    PIN_AddFiniFunction(Fini, 0);
#endif 
	/* start Pin */
	PIN_StartProgram();


	/* typically not reached; make the compiler happy */
	return EXIT_SUCCESS;

err:	/* error handling */

	/* detach from the process */
	libdft_die();

	/* return */
	return EXIT_FAILURE;
}
