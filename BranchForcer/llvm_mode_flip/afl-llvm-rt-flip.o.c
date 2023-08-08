/*
  Copyright 2015 Google LLC All rights reserved.
  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at:
    http://www.apache.org/licenses/LICENSE-2.0
  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
*/

/*
   american fuzzy lop - LLVM instrumentation bootstrap
   ---------------------------------------------------
   Written by Laszlo Szekeres <lszekeres@google.com> and
              Michal Zalewski <lcamtuf@google.com>
   LLVM integration design comes from Laszlo Szekeres.
   This code is the rewrite of afl-as.h's main_payload.
*/

#define _GNU_SOURCE
#include "../android-ashmem.h"
#include "../config.h"
#include "../types.h"

#include <stdio.h>
#include <stdlib.h>
#include <signal.h>
#include <unistd.h>
#include <string.h>
#include <assert.h>
#include <time.h>


#include <dlfcn.h>
#include <sys/syscall.h>

#include <sys/mman.h>
#include <sys/shm.h>
#include <sys/wait.h>
#include <sys/types.h>
#include <sys/ptrace.h>
#include <sys/reg.h>
#include <sys/syscall.h>
#include <sys/time.h>

/* This is a somewhat ugly hack for the experimental 'trace-pc-guard' mode.
   Basically, we need to make sure that the forkserver is initialized after
   the LLVM-generated runtime initialization pass, not before. */

#ifdef USE_TRACE_PC
#  define CONST_PRIO 5
#else
#  define CONST_PRIO 0
#endif /* ^USE_TRACE_PC */


#define TRACE_IT 1
#define NOT_TRIGGERED 10000000

/* Globals needed by the injected instrumentation. The __afl_area_initial region
   is used for instrumentation output before __afl_map_shm() has a chance to run.
   It will end up as .comm, so it shouldn't be too wasteful. */

u8  __afl_area_initial[MAP_SIZE];
u8* __afl_area_ptr = __afl_area_initial;

__thread u32 __afl_prev_loc;

/* Running in persistent mode? */

static u8 is_persistent;

/* Assign ID and flag*/
static u64 cond_id = (u64)(-2);
static int has_mutated = 0;
static u32 dry_run_flag = 1; 
static u32 branch_id = NOT_TRIGGERED;


/* SHM setup. */

static void __afl_map_shm(void) {

  u8 *id_str = getenv(SHM_ENV_VAR);

  /* If we're running under AFL, attach to the appropriate region, replacing the
     early-stage __afl_area_initial region that is needed to allow some really
     hacky .init code to work correctly in projects such as OpenSSL. */

  if (id_str) {

    u32 shm_id = atoi(id_str);

    __afl_area_ptr = shmat(shm_id, NULL, 0);

    /* Whooooops. */

    if (__afl_area_ptr == (void *)-1) _exit(1);

    /* Write something into the bitmap so that even with low AFL_INST_RATIO,
       our parent doesn't give up on us. */

    __afl_area_ptr[0] = 1;

  }

}


/* Fork server logic. */

static void __afl_start_forkserver(void) {

  static u8 tmp[8];
  s32 child_pid;

  /* Phone home and tell the parent that we're OK. If parent isn't there,
     assume we're not running in forkserver mode and just execute program. */

  if (write(FORKSRV_FD + 1, tmp, 4) != 4) return;

  while(1) {  
    u32 was_killed;
    int status;
    long orig_rax;

    /* Wait for parent by reading from the pipe. Abort if read fails. */
    if (read(FORKSRV_FD, tmp, 12) != 12) _exit(1);
    was_killed = *(u32 *)tmp;
    dry_run_flag = *(u32 *)(tmp + 4);
    branch_id = *(s32 *)(tmp + 8);

      if (dry_run_flag) {
        
        child_pid = fork();

        if (!child_pid) {
          close(FORKSRV_FD);
          close(FORKSRV_FD + 1);
#if TRACE_IT
          /* Trace me plz, I am ready */
          ptrace(PTRACE_TRACEME, child_pid, NULL, NULL);
          raise(SIGCONT);
#endif
          return;

        }

        /* Pass the child_pid to afl-fuzz, so it can kill child (handle_timeout in afl-fuzz.c) when timeout*/
        if (write(FORKSRV_FD + 1, &child_pid, 4) != 4) _exit(1);
        /* Set ptrace option */
        waitpid(-1, &status, 0);

#if TRACE_IT
        unsigned int opt = 0;
        opt |= PTRACE_O_TRACECLONE;
        opt |= PTRACE_O_TRACEFORK;
	      opt |= PTRACE_O_TRACEVFORK;
        ptrace(PTRACE_SETOPTIONS, child_pid, 0, opt);
        ptrace(PTRACE_SYSCALL, child_pid, NULL, NULL);

        while(1) {
          /* receive signal from any process */
          int sig_pid = waitpid(-1, &status, 0);

          /* HY: Properly handle different signals */
          if (WIFEXITED(status) && (sig_pid == child_pid)) {
            break;
          }
          
          if (WIFSIGNALED(status) && (WTERMSIG(status) == SIGSEGV)) {
            kill(sig_pid, SIGSEGV);
            break;
          }

          if (WIFSIGNALED(status) && (WTERMSIG(status) == SIGKILL)) {
            kill(sig_pid, SIGKILL);
            break;              
          }

          if (WSTOPSIG(status) == SIGTRAP) {
            orig_rax = ptrace(PTRACE_PEEKUSER, sig_pid, 8 * ORIG_RAX, 0);
            if (orig_rax == SYS_execve) {
              ptrace(PTRACE_DETACH, sig_pid, 0, 0);
            }
            __afl_area_ptr[orig_rax + 65536] = 1;
          }

          switch (status >> 8) {

            case (SIGTRAP | (PTRACE_EVENT_CLONE << 8)): 
              break;

            case (SIGTRAP | (PTRACE_EVENT_FORK << 8)):
              break;

            case (SIGTRAP | (PTRACE_EVENT_VFORK << 8)):
              break;

            case (SIGTRAP | (PTRACE_EVENT_EXEC << 8)):
              break;
          }  

          ptrace(PTRACE_SYSCALL, sig_pid, 0, 0);
        }
#endif

      } else {

          cond_id = branch_id;
          child_pid = fork();
          if (!child_pid) {

            close(FORKSRV_FD);
            close(FORKSRV_FD + 1);
            /* Trace me plz, I am ready */
#if TRACE_IT
            ptrace(PTRACE_TRACEME, child_pid, NULL, NULL);
            raise(SIGCONT);
#endif
            return;

          }
          
          /* Pass the child_pid to afl-fuzz, so it can kill child (handle_timeout in afl-fuzz.c) when timeout*/
          if (write(FORKSRV_FD + 1, &child_pid, 4) != 4) _exit(1);
          /* Set ptrace option */
          waitpid(-1, &status, 0);

#if TRACE_IT
          unsigned int opt = 0;
          opt |= PTRACE_O_TRACECLONE;
          opt |= PTRACE_O_TRACEFORK;
          opt |= PTRACE_O_TRACEVFORK;
          ptrace(PTRACE_SETOPTIONS, child_pid, 0, opt);
          ptrace(PTRACE_SYSCALL, child_pid, NULL, NULL);

          while(1) {
            int sig_pid = waitpid(-1, &status, 0);    

            if (WIFEXITED(status) && (sig_pid == child_pid)) {
              break;
            }
    
            if (WIFSIGNALED(status) && (WTERMSIG(status) == SIGSEGV)) {
              kill(sig_pid, SIGSEGV);
              break;
            }

            if (WIFSIGNALED(status) && (WTERMSIG(status) == SIGKILL)) {
              kill(sig_pid, SIGKILL);
              break;              
            }

            if (WIFSTOPPED(status) && WSTOPSIG(status) == SIGTRAP) {
              orig_rax = ptrace(PTRACE_PEEKUSER, sig_pid, 8 * ORIG_RAX, 0);
              if (orig_rax == SYS_execve) {
                ptrace(PTRACE_DETACH, sig_pid, 0, 0);
              }
              __afl_area_ptr[orig_rax + 65536] = 1;
            }

            switch (status >> 8) {

              case (SIGTRAP | (PTRACE_EVENT_CLONE << 8)): 
                break;

              case (SIGTRAP | (PTRACE_EVENT_FORK << 8)):
                break;

              case (SIGTRAP | (PTRACE_EVENT_VFORK << 8)):
                break;

              case (SIGTRAP | (PTRACE_EVENT_EXEC << 8)):
                break;
            }  

            ptrace(PTRACE_SYSCALL, sig_pid, 0, 0);
          }
#endif     
      }


      if (child_pid < 0) _exit(1);
      
    /* Relay wait status to pipe, then loop back. */

    if (write(FORKSRV_FD + 1, &status, 4) != 4) _exit(1);
  }

}


/* A simplified persistent mode handler, used as explained in README.llvm. */

int __afl_persistent_loop(unsigned int max_cnt) {

  static u8  first_pass = 1;
  static u32 cycle_cnt;

  if (first_pass) {

    /* Make sure that every iteration of __AFL_LOOP() starts with a clean slate.
       On subsequent calls, the parent will take care of that, but on the first
       iteration, it's our job to erase any trace of whatever happened
       before the loop. */

    if (is_persistent) {

      memset(__afl_area_ptr, 0, MAP_SIZE);
      __afl_area_ptr[0] = 1;
      __afl_prev_loc = 0;
    }

    cycle_cnt  = max_cnt;
    first_pass = 0;
    return 1;

  }

  if (is_persistent) {

    if (--cycle_cnt) {

      raise(SIGSTOP);

      __afl_area_ptr[0] = 1;
      __afl_prev_loc = 0;

      return 1;

    } else {

      /* When exiting __AFL_LOOP(), make sure that the subsequent code that
         follows the loop is not traced. We do that by pivoting back to the
         dummy output region. */

      __afl_area_ptr = __afl_area_initial;

    }

  }

  return 0;

}


/* This one can be called from user code when deferred forkserver mode
    is enabled. */

void __afl_manual_init(void) {

  static u8 init_done;

  if (!init_done) {

    __afl_map_shm();
    __afl_start_forkserver();
    init_done = 1;

  }

}


/* Proper initialization routine. */

__attribute__((constructor(CONST_PRIO))) void __afl_auto_init(void) {

  is_persistent = !!getenv(PERSIST_ENV_VAR);

  if (getenv(DEFER_ENV_VAR)) return;

  __afl_manual_init();

}


/* The following stuff deals with supporting -fsanitize-coverage=trace-pc-guard.
   It remains non-operational in the traditional, plugin-backed LLVM mode.
   For more info about 'trace-pc-guard', see README.llvm.
   The first function (__sanitizer_cov_trace_pc_guard) is called back on every
   edge (as opposed to every basic block). */

void __sanitizer_cov_trace_pc_guard(uint32_t* guard) {
  __afl_area_ptr[*guard]++;
}


/* Init callback. Populates instrumentation IDs. Note that we're using
   ID of 0 as a special value to indicate non-instrumented bits. That may
   still touch the bitmap, but in a fairly harmless way. */

void __sanitizer_cov_trace_pc_guard_init(uint32_t* start, uint32_t* stop) {

  u32 inst_ratio = 100;
  u8* x;

  if (start == stop || *start) return;

  x = getenv("AFL_INST_RATIO");
  if (x) inst_ratio = atoi(x);

  if (!inst_ratio || inst_ratio > 100) {
    fprintf(stderr, "[-] ERROR: Invalid AFL_INST_RATIO (must be 1-100).\n");
    abort();
  }

  /* Make sure that the first element in the range is always set - we use that
     to avoid duplicate calls (which can happen as an artifact of the underlying
     implementation in LLVM). */

  *(start++) = R(MAP_SIZE - 1) + 1;

  while (start < stop) {

    if (R(100) < inst_ratio) *start = R(MAP_SIZE - 1) + 1;
    else *start = 0;

    start++;

  }

}

/* Insert function to mutate the condition value of Br*/
int __flip_br_cond(uint8_t orig_cond, uint64_t id, char *br_loc) {
  
  if (dry_run_flag) {
    return orig_cond;
  }

  /* We only flip the branch when we first meet it */
  if (id != cond_id || has_mutated == 1){
    return orig_cond;
  }

  FILE *fd = fopen("./log/flip_result", "a");
  fprintf(fd, "%s\n", br_loc);
  fprintf(fd, "Flip branch %lld from %d to %d\n", cond_id, orig_cond, orig_cond ^ 1);
  fclose(fd);
  has_mutated = 1;
  return orig_cond ^ 1;
}
