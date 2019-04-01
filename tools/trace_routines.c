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

#include <stdio.h>
#include <stdlib.h>

#include "pin.H"
#include "branch_pred.h"
#include "libdft_api.h"

FILE *fp;
    
static void
trace_inspect(TRACE trace, VOID *v)
{

    RTN r = TRACE_Rtn(trace);
    if(RTN_Valid(r)){
   /*         string trace_rtn_str = RTN_Name(r);
            char *trace_rtn = (char *)malloc(trace_rtn_str.length() + 1);
            memset((void *)trace_rtn, 0, trace_rtn_str.length() + 1);
            strncpy(trace_rtn, trace_rtn_str.c_str(), trace_rtn_str.length());

            TRACE_InsertCall(trace, IPOINT_ANYWHERE, (AFUNPTR) print_trace_rtn, 
                    IARG_PTR, trace_rtn, IARG_END);*/
		    fprintf(fp, "%s\n",RTN_Name(r).c_str());
        }
    CODECACHE_FlushCache();
}

VOID Fini(INT32 code, VOID *v){
    fclose(fp);
}

int
main(int argc, char **argv)
{
	/* initialize symbol processing */
	PIN_InitSymbols();
	
	/* initialize PIN; optimized branch */
	if (unlikely(PIN_Init(argc, argv)))
		/* PIN initialization failed */
		goto err;
	
	/* register trace_ins() to be called for every trace */
	TRACE_AddInstrumentFunction(trace_inspect, NULL);

    fp = fopen("rtn_trace.log", "w");
    PIN_AddFiniFunction(Fini, 0);

	/* start PIN */
	PIN_StartProgram();

	/* typically not reached; make the compiler happy */
	return EXIT_SUCCESS;

err:
	/* error handling */

	/* return */
	return EXIT_FAILURE;
}
