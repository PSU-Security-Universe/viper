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

#include <sys/stat.h>
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
#include<sys/reg.h>
#include<sys/syscall.h>

/* This is a somewhat ugly hack for the experimental 'trace-pc-guard' mode.
   Basically, we need to make sure that the forkserver is initialized after
   the LLVM-generated runtime initialization pass, not before. */

#ifdef USE_TRACE_PC
#  define CONST_PRIO 5
#else
#  define CONST_PRIO 0
#endif /* ^USE_TRACE_PC */

#define log_cache_size 100
#define TRACE_DEBUG 0
#define VAL_DEBUG 0
#define USE_FLUSH 2

static u32 TRACE_WRITE_BYTES = 0;
static u32 TRACE_CACHE_BYTES = 0;

/* Globals needed by the injected instrumentation. The __afl_area_initial region
   is used for instrumentation output before __afl_map_shm() has a chance to run.
   It will end up as .comm, so it shouldn't be too wasteful. */

u8  __afl_area_initial[MAP_SIZE];
u8* __afl_area_ptr = __afl_area_initial;

/* HY: Similar to trace_bits, index represents branch id, 0 represents not triggered
   1 represents triggered */
u8 __orig_cond_map[MAP_SIZE];
u8* __orig_cond_ptr = __orig_cond_map;


__thread u32 __afl_prev_loc;


/* Running in persistent mode? */

static u8 is_persistent;

/* Assign ID and flag*/
static u64 cond_id = (u64)(-2);

static int has_mutated = 0;
static int syscall_counter = 0;

static u32 orig_cond_shm_id = 0;

/* 1 represents the first run */
static int dry_run_flag = 1; 

static u32 byte_index = 0;
static u32 val_byte_index = 0;

u8 *trace_log_cache;
u8 *val_log_cache;

FILE *trace_log;
FILE *val_log; 
FILE *store_load_log;
FILE *br_log;

#define TRACE_LOG_FILE      "./log/trace_log"
#define VAL_LOG_FILE        "./log/val_log"
#define STORE_LOAD_LOG_FILE "./log/store_load_log"
#define BR_LOG_FILE         "./log/br_log"

/* indicate whether main function has been executed */
u8 main_flag = 0;

u32 flip_mode = 0;
u32 flip_branch_id = 0;

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

  orig_cond_shm_id = shmget(IPC_PRIVATE, MAP_SIZE, IPC_CREAT | IPC_EXCL | 0600);
  __orig_cond_ptr = shmat(orig_cond_shm_id, NULL, 0);

}


/* Fork server logic. */

static void __afl_start_forkserver(void) {

  static u8 tmp[4];
  s32 child_pid;
  s32 inter_pid;
  u8  child_stopped = 0;
  u32 cond_id_index = 0;
  int counter = 0;
  /* Phone home and tell the parent that we're OK. If parent isn't there,
     assume we're not running in forkserver mode and just execute program. */

  if (write(FORKSRV_FD + 1, tmp, 4) != 4) return;

  while (cond_id_index < MAP_SIZE) {
    u32 was_killed;
    int status;
    long orig_rax;

    /* Wait for parent by reading from the pipe. Abort if read fails. */
    if (read(FORKSRV_FD, &was_killed, 4) != 4) _exit(1);

      if (dry_run_flag) {

        child_pid = fork();

        if (!child_pid) {
          close(FORKSRV_FD);
          close(FORKSRV_FD + 1);

          /* Trace me plz, I am ready */
          ptrace(PTRACE_TRACEME, 0, 0);
          raise(SIGCONT);

          return;
        }

        dry_run_flag = 0;

        /* Pass the child_pid to afl-fuzz, so it can kill child (handle_timeout in afl-fuzz.c) when timeout*/
        if (write(FORKSRV_FD + 1, &child_pid, 4) != 4) _exit(1);

        while(1) {

          waitpid(child_pid, &status, 0);

          if (WIFEXITED(status)) {
            break;
          }
          
          if (WSTOPSIG(status) == SIGSEGV) {
            kill(child_pid, SIGKILL);
            break;
          }

          if (WTERMSIG(status) == SIGKILL) {
            kill(child_pid, SIGKILL);
            break;
          }


          if (WSTOPSIG(status) == SIGTRAP) {
            orig_rax = ptrace(PTRACE_PEEKUSER, child_pid, 8 * ORIG_RAX, 0);
            fprintf(stderr, "[+] The child made a system call %ld.\n", orig_rax);
            __afl_area_ptr[orig_rax + 65536] = 1;

          }

          ptrace(PTRACE_SYSCALL, child_pid, 0, 0);
        }

      } else {
          while (__orig_cond_ptr[cond_id_index] == 0 && cond_id_index < (MAP_SIZE - 1)) cond_id_index++;
          counter++;
          cond_id = cond_id_index;
          cond_id_index++;
          fprintf(stderr, "cond_id: %d\n", cond_id);

          child_pid = fork();
            
          if (!child_pid) {
            
            close(FORKSRV_FD);
            close(FORKSRV_FD + 1);

            /* Trace me plz, I am ready */
            ptrace(PTRACE_TRACEME, 0, 0);
            raise(SIGCONT);

            return;
          }

          if (write(FORKSRV_FD + 1, &child_pid, 4) != 4) _exit(1);

          while(1) {

            waitpid(child_pid, &status, 0);

            if (WIFEXITED(status)) {
              break;
            }
    
            if (WSTOPSIG(status) == SIGSEGV) {
              kill(child_pid, SIGKILL);
              break;
            }

            if (WTERMSIG(status) == SIGKILL) {
              kill(child_pid, SIGKILL);
              break;
            }

            if (WSTOPSIG(status) == SIGTRAP) {
              orig_rax = ptrace(PTRACE_PEEKUSER, child_pid, 8 * ORIG_RAX, 0);
              __afl_area_ptr[orig_rax + 65536] = 1;
            }

            ptrace(PTRACE_SYSCALL, child_pid, 0, 0);
          }
        fprintf(stderr, "the length is:%d\n", counter);     
      }

      if (child_pid < 0) _exit(1);

    /* Child process ends before parent process --> trigger this __exit(1) 
       Normally don't happen, but happen when we trace syscalls, so turn off it.
    */
    // if (waitpid(child_pid, &status, is_persistent ? WUNTRACED : 0) < 0) {
    //   _exit(1);
    // }

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

void save_remaining_data_to_disk() {

  if (trace_log == NULL) {
    perror("failed to open trace_log");
  }
  size_t write_nmemb = fwrite(trace_log_cache, 1, byte_index, trace_log);
  if (write_nmemb != byte_index)
    perror("failed to write data to trace_log in signal handler");
#if TRACE_DEBUG
  else
    TRACE_WRITE_BYTES += byte_index;
  fprintf(stderr, "Trace log cached bytes: %d, wrote bytes: %d\n", TRACE_CACHE_BYTES, TRACE_WRITE_BYTES);
#endif
  fclose(trace_log);

  fclose(store_load_log);
  fclose(br_log);

  write_nmemb = fwrite(val_log_cache, 1, val_byte_index, val_log);
  if (write_nmemb != val_byte_index)
    perror("failed to write data to val_log in signal handler");
  fclose(val_log);

}

void __sigterm_handler(int signum) {
  fprintf(stderr, "Caught SIGTERM/SIGSEGV signal.\n");
  save_remaining_data_to_disk();
  kill(getpid(), SIGKILL);
}


int __register_signal_handler() {
  struct sigaction action;
  memset(&action, 0, sizeof(action));
  action.sa_handler = __sigterm_handler;
  if (sigaction(SIGTERM, &action, NULL) < 0) {
    perror("sigterm error");
  } 
  if (sigaction(SIGSEGV, &action, NULL) < 0) {
    perror("sigsegv error");
  } 
  return 1;
}


/* Proper initialization routine. */

__attribute__((constructor(CONST_PRIO))) void __afl_auto_init(void) {

  mkdir("log", 0666);
  uint32_t pid = getpid();
  char pid_str[200];
  remove("./log/proc_map");
  sprintf(pid_str, "cp /proc/%d/maps ./log/proc_map", pid);
  system(pid_str);

  remove(TRACE_LOG_FILE);
  trace_log = fopen(TRACE_LOG_FILE, "ab");
  remove(VAL_LOG_FILE);
  val_log = fopen(VAL_LOG_FILE, "ab");
  remove(STORE_LOAD_LOG_FILE);
  store_load_log = fopen(STORE_LOAD_LOG_FILE, "ab");
  remove(BR_LOG_FILE);
  br_log = fopen(BR_LOG_FILE, "ab");

  trace_log_cache = (u8*)malloc(log_cache_size);
  memset(trace_log_cache, 0, log_cache_size);
  val_log_cache = (u8*)malloc(log_cache_size);
  memset(val_log_cache, 0, log_cache_size);

  __register_signal_handler();

  is_persistent = !!getenv(PERSIST_ENV_VAR);

  if (getenv(DEFER_ENV_VAR)) return;

  __afl_manual_init();

}

void __attribute__((destructor(CONST_PRIO))) destructor() {
  save_remaining_data_to_disk();
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

void load_cache_to_file() {

  if (trace_log == NULL) {
    perror("failed to open trace_log");
  }
  size_t write_nmemb = fwrite(trace_log_cache, 1, byte_index, trace_log);
  if (write_nmemb != byte_index)
    perror("failed to write data to trace_log");
#if TRACE_DEBUG
  else
    TRACE_WRITE_BYTES += byte_index;
  fprintf(stderr, "Trace log cached bytes: %d, wrote bytes: %d\n", TRACE_CACHE_BYTES, TRACE_WRITE_BYTES);
#endif


#if USE_FLUSH
  fflush(trace_log);
  fflush(br_log);
  fflush(store_load_log);
  fflush(val_log);
#endif

  memset(trace_log_cache, 0, log_cache_size);
  byte_index = 0;
  return;
}

void val_load_cache_to_file() {

  size_t write_nmemb = fwrite(val_log_cache, 1, log_cache_size, val_log);
  if (write_nmemb != log_cache_size)
    perror("failed to write data to val_log");

#if USE_FLUSH >= 2
  fflush(trace_log);
  fflush(br_log);
  fflush(store_load_log);
  fflush(val_log);
#endif

  memset(val_log_cache, 0, log_cache_size);
  val_byte_index = 0;
  return;
}

int __main_flag() {
  const char *env_flip_mode = getenv("FLIP_MODE");
  const char *env_flip_branch_id = getenv("FLIP_BRANCH_ID");

  if (!env_flip_mode || !env_flip_branch_id) {
    fprintf(stderr, "[-] ERROR: Please set env `FLIP_MODE` and `FLIP_BRANCH_ID`.\n");
    abort();
  }

  flip_mode = atoi(env_flip_mode);
  flip_branch_id = atoi(env_flip_branch_id);
  main_flag = 1; 

  return 1;
}

int __record_store_ptr(uint64_t store_address, uint64_t w_id) {
  
  if (!main_flag) {
    return 1;
  }

  store_address = store_address | 0x0001000000000000;

  size_t write_nmemb = fwrite(&store_address, 8, 1, store_load_log);
  if (write_nmemb != 1)
    perror("failed to write store address to store_load_log");

  write_nmemb = fwrite(&w_id, 8, 1, store_load_log);
  if (write_nmemb != 1)
    perror("failed to write store id to store_load_log");
  
#if USE_FLUSH >= 2
  fflush(store_load_log);
#endif

  return 1;
}

int __record_load_ptr(uint64_t load_address, uint64_t r_id) {
  if (!main_flag) {
    return 1;
  }

  load_address = load_address | 0x0002000000000000;

  size_t write_nmemb = fwrite(&load_address, 8, 1, store_load_log);
  if (write_nmemb != 1)
    perror("failed to write load address to store_load_log");

  fwrite(&r_id, 8, 1, store_load_log);
  if (write_nmemb != 1)
    perror("failed to write load id to store_load_log");

#if USE_FLUSH >= 2
  fflush(store_load_log);
#endif

  return 1;
}

int __record_callback(uint32_t flag) {
  u64 callback_flag;
  if (!main_flag) {
    return 1;
  }

  size_t write_nmemb;

  if (!flag) {
    callback_flag = 0xAAAAAAAAAAAAAAAA;
  } else {
    callback_flag = 0xBBBBBBBBBBBBBBBB;
  }

    write_nmemb = fwrite(&callback_flag, 8, 1, store_load_log);
    if (write_nmemb != 1)
      perror("failed to write callback flag to store_load_log");

    write_nmemb = fwrite(&callback_flag, 8, 1, br_log);
    if (write_nmemb != 1)
      perror("failed to write callback flag to br_log");

#if USE_FLUSH >= 2
  fflush(store_load_log);
  fflush(br_log);
#endif

  return 1;
}

int __record_memcpy_ptr(uint64_t memcpy_dst, uint64_t memcpy_src, uint64_t memcpy_size) {
  if (store_load_log == NULL || !main_flag) {
    return 1;
  }

  memcpy_dst = memcpy_dst | 0x0003000000000000;
  memcpy_src = memcpy_src | 0x0003000000000000;
  memcpy_size = memcpy_size | 0x0003000000000000;

  size_t write_nmemb = fwrite(&memcpy_dst, 8, 1, store_load_log);
  if (write_nmemb != 1)
    perror("failed to write dest of memcpy to store_load_log");

  write_nmemb = fwrite(&memcpy_src, 8, 1, store_load_log);
  if (write_nmemb != 1)
    perror("failed to write src of memcpy to store_load_log");

  write_nmemb = fwrite(&memcpy_size, 8, 1, store_load_log);
  if (write_nmemb != 1)
    perror("failed to write size of memcpy to store_load_log");

#if USE_FLUSH >= 2
  fflush(store_load_log);
#endif

  return 1;
}

int __record_memset_ptr(uint64_t memset_dst, uint64_t memset_size) {
  if (store_load_log == NULL || !main_flag) {
    return 1;
  }

  memset_dst = memset_dst | 0x0004000000000000;
  memset_size = memset_size | 0x0004000000000000;

  size_t write_nmemb = fwrite(&memset_dst, 8, 1, store_load_log);
  if (write_nmemb != 1)
    perror("failed to write dest of memset to store_load_log");

  write_nmemb = fwrite(&memset_size, 8, 1, store_load_log);
  if (write_nmemb != 1)
    perror("failed to write size of memset to store_load_log");

#if USE_FLUSH >= 2
  fflush(store_load_log);
#endif

  return 1;
}

int __record_indirect_call(uint64_t call_address, uint64_t id) {
  if (!main_flag) {
    return 1;
  }

  id |= (0x2UL << 62);
  size_t write_nmemb = fwrite(&id, 8, 1, br_log);
  if (write_nmemb != 1)
    perror("failed to write indirect call address to br_log");

#if USE_FLUSH >= 2
  fflush(br_log);
#endif

  int byte_left =log_cache_size - byte_index;
  if (byte_left < 16) {
    load_cache_to_file();
  }

  *(uint64_t *)&trace_log_cache[byte_index] = call_address;
  byte_index += 8;

#if TRACE_DEBUG == 1 
  TRACE_CACHE_BYTES += 8;
  fprintf(stderr, "trace_log(indirect): u64 %ld\n", call_address);
  fprintf(stderr, "Trace log cached bytes: %d, wrote bytes: %d\n", TRACE_CACHE_BYTES, TRACE_WRITE_BYTES);
#endif 

  if(val_byte_index == log_cache_size) {
    val_load_cache_to_file();
  } 
  val_log_cache[val_byte_index] = 2;
  val_byte_index++; 

#if VAL_DEBUG==1
  fprintf(stderr, "val_log: 2\n");
#endif

  return 1;
}

int __flip_switch_cond(uint32_t orig_cond, uint64_t id) {
  if (!main_flag) {
    return 1;
  }

  id |= (0x1UL << 62);
  size_t write_nmemb = fwrite(&id, 8, 1, br_log);
  if (write_nmemb != 1)
    perror("failed to write switch condition to br_log");

#if USE_FLUSH >= 2
  fflush(br_log);
#endif

  int byte_left = log_cache_size - byte_index;
  if (byte_left < 4) {
    load_cache_to_file();
  }

  *(uint32_t *)&trace_log_cache[byte_index] = orig_cond;
  byte_index += 4;

#if TRACE_DEBUG == 1
  TRACE_CACHE_BYTES += 4;
  fprintf(stderr, "trace_log(switch): u32 %d\n", orig_cond);
  fprintf(stderr, "Trace log cached bytes: %d, wrote bytes: %d\n", TRACE_CACHE_BYTES, TRACE_WRITE_BYTES);
#endif 

  if(val_byte_index == log_cache_size) {
    val_load_cache_to_file();
  } 
  val_log_cache[val_byte_index] = 1;
  val_byte_index++; 

#if VAL_DEBUG==1
  fprintf(stderr, "val_log: 1\n");
#endif

  return 1;
}

/* Insert function to mutate the condition value of Br*/
int __flip_br_cond(uint8_t orig_cond, uint64_t id, char *br_loc) {

  if (!main_flag) {
    return orig_cond;
  }

  size_t write_nmemb = fwrite(&id, 8, 1, br_log);
  if (write_nmemb != 1)
    perror("failed to write branch condition to br_log");

#if USE_FLUSH >= 2
  fflush(br_log);
#endif

  if (byte_index == log_cache_size) {
    load_cache_to_file();
  }

  if (flip_mode == 1 && flip_branch_id == id && !has_mutated) {
    orig_cond = orig_cond ^ 1;
    has_mutated = 1;
  }
  
  trace_log_cache[byte_index] = orig_cond & 0x01;
  byte_index++;

#if TRACE_DEBUG == 1
  TRACE_CACHE_BYTES += 1;
  fprintf(stderr, "trace_log(branch): u8, id: %ld, value: %d\n", id, orig_cond & 0x01);
  fprintf(stderr, "Trace log cached bytes: %d, wrote bytes: %d\n", TRACE_CACHE_BYTES, TRACE_WRITE_BYTES);
#endif 


  if(val_byte_index == log_cache_size) {
    val_load_cache_to_file();
  } 
  val_log_cache[val_byte_index] = 0;
  val_byte_index++; 

#if VAL_DEBUG==1
  fprintf(stderr, "val_log: 0\n");
#endif

  return orig_cond;

}
