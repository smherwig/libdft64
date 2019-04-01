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

#ifndef __LIBDFT_API_H__
#define __LIBDFT_API_H__

#include <sys/syscall.h>
#include <linux/version.h>
#include <fstream>
#include <iostream>

#include "pin.H"

typedef unsigned __int128 uint128_t;
typedef uint128_t uint256_t[2];
typedef uint128_t uint512_t[4];

//TODO: determine max syscall number based on kernel version
#define SYSCALL_MAX 331
#if 0 
#if LINUX_VERSION_CODE < KERNEL_VERSION(2,6,26)
#error "Your kernel is tool old and this version of libdft does not support it"
#elif LINUX_VERSION_CODE == KERNEL_VERSION(2,6,26)
#define SYSCALL_MAX	__NR_timerfd_gettime+1	/* max syscall number */
#elif LINUX_VERSION_CODE >= KERNEL_VERSION(2,6,27) && \
		LINUX_VERSION_CODE <= KERNEL_VERSION(2,6,29)
#define SYSCALL_MAX	__NR_inotify_init1+1	/* max syscall number */
#elif LINUX_VERSION_CODE == KERNEL_VERSION(2,6,30)
#define SYSCALL_MAX	__NR_pwritev+1		/* max syscall number */
#elif LINUX_VERSION_CODE == KERNEL_VERSION(2,6,31)
#define SYSCALL_MAX	__NR_perf_counter_open+1/* max syscall number */
#elif LINUX_VERSION_CODE == KERNEL_VERSION(2,6,32)
#define SYSCALL_MAX	__NR_perf_event_open+1	/* max syscall number */
#elif LINUX_VERSION_CODE >= KERNEL_VERSION(2,6,33) && \
		LINUX_VERSION_CODE <= KERNEL_VERSION(2,6,35)
#define SYSCALL_MAX	__NR_recvmmsg+1		/* max syscall number */
#elif LINUX_VERSION_CODE >= KERNEL_VERSION(2,6,36) && \
		LINUX_VERSION_CODE <= KERNEL_VERSION(2,6,38)
#define SYSCALL_MAX	__NR_prlimit64+1	/* max syscall number */
#else
#define SYSCALL_MAX	__NR_syncfs+1		/* max syscall number */
#endif
#endif

#define LOGFILE "libdft.log"

#define INIT_BUF_CAP 32

/* FIXME: turn off the EFLAGS.AC bit by applying the corresponding mask */
#define CLEAR_EFLAGS_AC(eflags)	((eflags & 0xfffbffff))

#define VCPU_MASK32	0xFFU			/* 32-bit VCPU mask */
#define VCPU_MASK16	0xFFFFU			/* 16-bit VCPU mask */
#define VCPU_MASK8	0x01			/* 8-bit VCPU mask */

#define YMM_BITS        256
#define XMM_BITS        128
#define BYTE_BITS       8
#define WORD_BITS       16
#define DWORD_BITS      32
#define QWORD_BITS      64
#define DQWORD_BITS     128
#define QQWORD_BITS     256

#define MEM_LLONG_LEN   64
#define MEM_LONG_LEN	32			/* long size (32-bit) */
#define MEM_WORD_LEN	16			/* word size (16-bit) */
#define MEM_BYTE_LEN	8			/* byte size (8-bit) */
#define BIT2BYTE(len)	((len) >> 3)		/* scale change; macro */
#define BYTE2BIT(len)   ((len) << 3)
#define BIT2WORD(len)   ((len) >> 4)
#define BIT2DWORD(len)  ((len) >> 5)
#define BIT2QWORD(len)  ((len) >> 6)

#define SHIFT_MASK      0x001FU  /* mask count operand for shifts to 5 bits */
#define SHIFT_MASK64    0x003FU  /* mask count operand for shifts to 6 bits */
#define TRUE_MASK8      0x00FFU
#define HIGH_BIT_SET    0x0080U
#define LOW4BITS_MASK   0x000FU
#define LOW2BITS_MASK   0x0003U
#define BIT0MASK        0x0001U
#define BIT4MASK        0x0004U

// used on count operand in shift instructions to compute (count / 8)
#define BYTE_ALIGN(value)    (value & 0xFFFFFFFFFFFFFFF8)   

//#define INS_INSTRUMENT
#define TRACE_INSTRUMENT 

#define DEBUG 
//#define PROPAGATION_DEBUG //prints taints after instructions operating on tainted data
//#define DEBUG_MEMTRACK //logs page allocation info
//#define INS_DEBUG //logs all instrutions executed
//#define TRACK_UNHANDLED_INS //prints to stdout all instructions not handled
//#define ALL_ANALYSIS_DEBUG //prints taints after all instructions
//#define TAGMAP_DEBUG
//#define SYSCALL_DEBUG

void printLog(const char*, ...);

enum {
/* #define */ SYSCALL_ARG0 = 0,			/* 1st argument in syscall */
/* #define */ SYSCALL_ARG1 = 1,			/* 2nd argument in syscall */
/* #define */ SYSCALL_ARG2 = 2,			/* 3rd argument in syscall */
/* #define */ SYSCALL_ARG3 = 3,			/* 4th argument in syscall */
/* #define */ SYSCALL_ARG4 = 4,			/* 5th argument in syscall */
/* #define */ SYSCALL_ARG5 = 5,			/* 6th argument in syscall */
/* #define */ SYSCALL_ARG_NUM = 6		/* syscall arguments */
};

enum {						 /* {en,dis}able (ins_desc_t) */
/* #define */ INSDFL_ENABLE	= 0,
/* #define */ INSDFL_DISABLE	= 1
};


#define GPR_NUM		16			/* general purpose registers */
#define MMX_NUM     8
#define AVX_NUM     16
#define AVX_SCRATCH  16
// 64-bit gpr register names
enum{
    //gpr
    RAX,
    RBX,
    RCX,
    RDX,
    RBP,
    RSI,
    RDI,
    RSP,
    R8,
    R9,
    R10,
    R11,
    R12,
    R13,
    R14,
    R15,
    GPR_SCRATCH
};


// 16-bit registers
enum{
    AX,
    BX,
    CX,
    DX,
    BP,
    SI,
    DI,
    SP
};

/*
 * virtual CPU (VCPU) context definition;
 * x64
 */
typedef struct {
	/*
	 * registers tag structure
	 */
	ADDRINT gpr[GPR_NUM + 1];
    UINT64 mmx[MMX_NUM + 1];
    uint256_t avx[AVX_NUM + 1];
} vcpu_ctx_t;

/*
 * system call context definition
 *
 * only up to SYSCALL_ARGS (i.e., 6) are saved
 */
typedef struct {
	ADDRINT nr;			/* syscall number */
	ADDRINT arg[SYSCALL_ARG_NUM];	/* arguments */
	ADDRINT ret;			/* return value */
	void	*aux;			/* auxiliary data (processor state) */
/* 	ADDRINT errno; */		/* error code */
} syscall_ctx_t;

/* thread context definition */
typedef struct {
	vcpu_ctx_t	vcpu;		/* VCPU context */
	syscall_ctx_t	syscall_ctx;	/* syscall context */
	void		*uval;		/* local storage */
} thread_ctx_t;

/* instruction (ins) descriptor */
typedef struct {
	void 	(* pre)(INS ins);	/* pre-ins instrumentation callback */
	void 	(* post)(INS ins);	/* post-ins instrumentation callback */
	size_t	dflact;			/* default instrumentation predicate */
} ins_desc_t;


/* libdft API */
int	libdft_init(void);
void libdft_die(void);
void printPageTaints();
void printPageAndByteTaints();
void printRegTaints(const CONTEXT*);
int getTaintedPagesBuf(ADDRINT **taintedPages);
void freeTaintedPagesBuf(ADDRINT *taintedPages);
string uint128_hex_string(uint128_t *num);
string uint256_hex_string(uint256_t *num);
string uint512_hex_string(uint512_t *num);


/* ins API */
int	ins_set_pre(ins_desc_t*, void (*)(INS));
int	ins_clr_pre(ins_desc_t*);
int	ins_set_post(ins_desc_t*, void (*)(INS));
int	ins_clr_post(ins_desc_t*);
int	ins_set_dflact(ins_desc_t *desc, size_t action);
#if 0
/* REG API */
size_t	REG64_INDX(REG);
size_t	REG16_INDX(REG);
size_t	REG8_INDX(REG);
UINT32 MM_INDX(REG);
UINT32 XMM_INDX(REG);
UINT32 YMM_INDX(REG);
#endif
#endif /* __LIBDFT_API_H__ */
