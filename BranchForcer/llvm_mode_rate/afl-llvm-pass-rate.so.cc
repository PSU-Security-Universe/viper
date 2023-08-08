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
   american fuzzy lop - LLVM-mode instrumentation pass
   ---------------------------------------------------

   Written by Laszlo Szekeres <lszekeres@google.com> and
              Michal Zalewski <lcamtuf@google.com>

   LLVM integration design comes from Laszlo Szekeres. C bits copied-and-pasted
   from afl-as.c are Michal's fault.

   This library is plugged into LLVM when invoking clang through afl-clang-fast-rate.
   It tells the compiler to add code roughly equivalent to the bits discussed
   in ../afl-as.h.
*/

#define AFL_LLVM_PASS

#include "../config.h"
#include "../debug.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <fstream>
#include <iostream>

#include "llvm/ADT/Statistic.h"
#include <llvm/ADT/StringRef.h>
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/CFG.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
using namespace std;

namespace {

  class AFLCoverage : public ModulePass {

    public:

      IntegerType *Int1Ty   = nullptr;
      IntegerType *Int8Ty   = nullptr;
      IntegerType *Int32Ty  = nullptr;
      IntegerType *Int64Ty  = nullptr;
      PointerType *Ptr8Ty   = nullptr;

      static char ID;
      AFLCoverage() : ModulePass(ID) { }
      bool runOnModule(Module &M) override;

      bool insertMainFlag(Function *func, BasicBlock::iterator IP);

      bool insertFunctionCondBr(Function *func, BranchInst *BI);
      bool insertFunctionSwitch(Function *func, SwitchInst *SI);
      
      bool insertFunctionIndirectCall(Function *func, CallInst *CI);
      bool insertFunctionIndirectCall(Function *func, InvokeInst *II);
      
      bool insertFunctionStore(Function *func, StoreInst *SI);
      bool insertFunctionLoad(Function *func, LoadInst *LI);

      bool insertFunctionMemcpy(Function *func, CallInst *CI);

      bool insertFunctionMemset(Function *func, CallInst *CI);

      bool insertRecordCallback(Function *func, CallInst *CI);
      bool insertRecordCallback(Function *func, InvokeInst *II);
  };

}

uint64_t branch_id = 0;
uint64_t switch_id = 0;
uint64_t icall_id = 0;
uint64_t rw_id = 0;

char AFLCoverage::ID = 0;


vector<string> callbackNameList = {
  "qsort", "bsearch", 
  "jpeg_write_coefficients",
  "jpeg_finish_compress",
  "jpeg_finish_decompress",
  "jpeg_read_header",
  "XML_Parse",
  "pthread_once",
  "pam_authenticate"
 };
vector<string> invokeCallbackNameList = {
  "XML_Parse",
};

inline string trim(string& str) {
    str.erase(str.find_last_not_of(' ')+1);      
    str.erase(0, str.find_first_not_of(' '));    
    return str;
}

void loadCallbackNameList() {
  string CALLBACKFILE = "callbacks";
  if (access(CALLBACKFILE.c_str(), F_OK)) { 
    errs() << "Not found callbacks.\n";
    exit(1);
  }

  ifstream libcall_file(CALLBACKFILE);
  string line;
  while (getline(libcall_file, line)) {
    callbackNameList.push_back(trim(line));
  }
}


bool AFLCoverage::runOnModule(Module &M) {

  LLVMContext &C = M.getContext();

  Int1Ty = IntegerType::getInt1Ty(C);
  Int8Ty  = IntegerType::getInt8Ty(C);
  Int32Ty = IntegerType::getInt32Ty(C);
  Int64Ty = IntegerType::getInt64Ty(C);
  Ptr8Ty = PointerType::getInt8PtrTy(C);

  /* Show a banner */

  char be_quiet = 0;

  if (isatty(2) && !getenv("AFL_QUIET")) {

    SAYF(cCYA "afl-llvm-pass-rate " cBRI VERSION cRST " by <lszekeres@google.com>\n");

  } else be_quiet = 1;

  /* Decide instrumentation ratio */

  char* inst_ratio_str = getenv("AFL_INST_RATIO");
  unsigned int inst_ratio = 100;

  if (inst_ratio_str) {

    if (sscanf(inst_ratio_str, "%u", &inst_ratio) != 1 || !inst_ratio ||
        inst_ratio > 100)
      FATAL("Bad value of AFL_INST_RATIO (must be between 1 and 100)");

  }

  /* Get globals for the SHM region and the previous location. Note that
     __afl_prev_loc is thread-local. */

  GlobalVariable *AFLMapPtr =
      new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");

  /* Instrument all the things! */

  int inst_blocks = 0;

  /* Prepare for the function insertion */
  /* Int1Ty->return value, Int8Ty->original condition value, Int64Ty->branch*/
  vector<Type *> args0 = {Int8Ty, Int64Ty, Ptr8Ty};
  auto *br_helpTy = FunctionType::get(Int1Ty, args0, false);
  Function *flip_br_cond = dyn_cast<Function>(M.getOrInsertFunction("__flip_br_cond", br_helpTy));

  vector<Type *> args1 = {Int32Ty, Int64Ty};
  auto *switch_helpTy = FunctionType::get(Int32Ty, args1, false);
  Function *flip_switch_cond = dyn_cast<Function>(M.getOrInsertFunction("__flip_switch_cond", switch_helpTy));

  vector<Type *> args2 = {Int64Ty, Int64Ty};
  auto *indirect_call_helpTy = FunctionType::get(Int32Ty, args2, false);
  Function *record_indirect_call = dyn_cast<Function>(M.getOrInsertFunction("__record_indirect_call", indirect_call_helpTy));

  vector<Type *> args3 = {Int64Ty, Int64Ty};
  auto *store_ptr_helpTy = FunctionType::get(Int32Ty, args3, false);
  Function *record_store_ptr = dyn_cast<Function>(M.getOrInsertFunction("__record_store_ptr", store_ptr_helpTy));

  vector<Type *> args4 = {Int64Ty, Int64Ty};
  auto *load_ptr_helpTy = FunctionType::get(Int32Ty, args4, false);
  Function *record_load_ptr = dyn_cast<Function>(M.getOrInsertFunction("__record_load_ptr", load_ptr_helpTy));

  vector<Type *> args5 = {Int64Ty, Int64Ty, Int64Ty};
  auto *memcpy_ptr_helpTy = FunctionType::get(Int32Ty, args5, false);
  Function *record_memcpy_ptr = dyn_cast<Function>(M.getOrInsertFunction("__record_memcpy_ptr", memcpy_ptr_helpTy));

  vector<Type *> args6 = {Int64Ty, Int64Ty};
  auto *memset_ptr_helpTy = FunctionType::get(Int32Ty, args6, false);
  Function *record_memset_ptr = dyn_cast<Function>(M.getOrInsertFunction("__record_memset_ptr", memset_ptr_helpTy));

  vector<Type *> args7 = {};
  auto *main_flag_helpTy = FunctionType::get(Int1Ty, args7, false);
  Function *main_flag = dyn_cast<Function>(M.getOrInsertFunction("__main_flag", main_flag_helpTy));

  vector<Type *> args8 = {Int32Ty};
  auto *record_callback_helpTy = FunctionType::get(Int1Ty, args8, false);
  Function *record_callback = dyn_cast<Function>(M.getOrInsertFunction("__record_callback", record_callback_helpTy));

  for (auto &F : M) {
    for (auto &BB : F) {
      
      if ((F.getName() == "main") && (&BB == &(F.getEntryBlock()))) {
        BasicBlock::iterator IP = BB.getFirstInsertionPt();
        this->insertMainFlag(main_flag, IP);
      }

      BasicBlock::iterator IP = BB.getFirstInsertionPt();
      IRBuilder<> IRB(&(*IP));

      if (AFL_R(100) >= inst_ratio) continue;

      /* Make up cur_loc */
      /* last 4K for recording syscall */
      unsigned int cur_loc = AFL_R(MAP_SIZE - 4 * 1024);

      ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc);
      for (auto &I : BB) {
          if (BranchInst *BI = dyn_cast<BranchInst>(&I)) {
            if (BI->isConditional())
              this->insertFunctionCondBr(flip_br_cond, BI);
          }
          else if (SwitchInst *SI = dyn_cast<SwitchInst>(&I)) {
            this->insertFunctionSwitch(flip_switch_cond, SI);
          }
          else if (CallInst *CI = dyn_cast<CallInst>(&I)) {
            if (CI->getCalledFunction() == nullptr) {
              this->insertFunctionIndirectCall(record_indirect_call, CI);
            } else {
              StringRef funcName = CI->getCalledFunction()->getName();

              if (funcName ==  "llvm.memcpy.p0i8.p0i8.i64") {
                this->insertFunctionMemcpy(record_memcpy_ptr, CI);
              } else if (funcName ==  "llvm.memset.p0i8.i64") {
                this->insertFunctionMemset(record_memset_ptr, CI);
              } else if (find(callbackNameList.begin(), callbackNameList.end(),
                              funcName) != callbackNameList.end()) {
                this->insertRecordCallback(record_callback, CI);
              }
            }
          }
          else if (InvokeInst *II = dyn_cast<InvokeInst>(&I)) {
            if (II->getCalledFunction() == nullptr) {
              this->insertFunctionIndirectCall(record_indirect_call, II);
            } else {
                StringRef funcName = II->getCalledFunction()->getName();

                if (find(invokeCallbackNameList.begin(), invokeCallbackNameList.end(),
                        funcName) != invokeCallbackNameList.end()) {
                  this->insertRecordCallback(record_callback, II);
                } 
            }
          }


          else if (StoreInst *StI = dyn_cast<StoreInst>(&I)) {
            this->insertFunctionStore(record_store_ptr, StI);
          }
          else if (LoadInst *LI = dyn_cast<LoadInst>(&I)) {
            this->insertFunctionLoad(record_load_ptr, LI);
          }
      }
      
      /* Load SHM pointer */
      LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
      MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      /* Get the corresponding element */
      Value *MapPtrIdx = IRB.CreateGEP(MapPtr, CurLoc);
      /* Set the bit */
      StoreInst *SI = IRB.CreateStore(ConstantInt::get(Int8Ty, 1), MapPtrIdx);
      SI->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      inst_blocks++;

    }

  }

  if (!be_quiet) {

    if (!inst_blocks) WARNF("No instrumentation targets found.");
    else OKF("Instrumented %u locations (%s mode, ratio %u%%).",
             inst_blocks, getenv("AFL_HARDEN") ? "hardened" :
             ((getenv("AFL_USE_ASAN") || getenv("AFL_USE_MSAN")) ?
              "ASAN/MSAN" : "non-hardened"), inst_ratio);

  }
  return true;

}

bool AFLCoverage::insertMainFlag(Function *func, BasicBlock::iterator IP) {
  IRBuilder<> IRB(&(*IP));
  std::vector<Value *> args = {};
  IRB.CreateCall(func, args);
  return true;
}

bool AFLCoverage::insertRecordCallback(Function *func, InvokeInst *II) {
  IRBuilder<> IRB(&(*II));
  auto *flag = IRB.getInt32(0);
  std::vector<Value *> args = {flag};
  IRB.CreateCall(func, args);  

  IRB.SetInsertPoint(II->getNormalDest(), 
                     II->getNormalDest()->getFirstInsertionPt());
  flag = IRB.getInt32(1);
  args = {flag};
  IRB.CreateCall(func, args);
  return true;
}

bool AFLCoverage::insertRecordCallback(Function *func, CallInst *CI) {
  IRBuilder<> IRB(&(*CI));
  auto *flag = IRB.getInt32(0);
  std::vector<Value *> args = {flag};
  IRB.CreateCall(func, args);  

  IRB.SetInsertPoint(CI->getNextNode());
  flag = IRB.getInt32(1);
  args = {flag};
  IRB.CreateCall(func, args);
  return true;
}

bool AFLCoverage::insertFunctionCondBr(Function *func, BranchInst *BI) {
  IRBuilder<> IRB(&(*BI));
  /* get instruction location */
  const DILocation *DIB = BI->getDebugLoc();
  string debug_info;
  if (DIB != nullptr) {
    debug_info = DIB->getDirectory().str() + "/" + DIB->getFilename().str() + ":" + to_string(DIB->getLine());
  } else {
    debug_info = "no debug info";
  }
  Value *br_loc = IRB.CreateGlobalStringPtr(debug_info.c_str());  
  Value *br_cond = BI->getCondition();
  auto *br_id = IRB.getInt64(branch_id++);
  std::vector<Value *> args = {IRB.CreateZExt(br_cond, Int8Ty), br_id, br_loc};
  Value *new_br_cond = IRB.CreateCall(func, args);
  BI->setCondition(new_br_cond);  
  return true;
}

bool AFLCoverage::insertFunctionSwitch(Function *func, SwitchInst *SI) {
  IRBuilder<> IRB(SI);
  /* get instruction location */
  Value *switch_cond = SI->getCondition();

  LLVMContext &C = SI->getContext();
  IntegerType *Int32Ty = IntegerType::getInt32Ty(C);
  Value *switch_cond_new = IRB.CreateZExtOrTrunc(switch_cond, Int32Ty);
  
  auto *br_id = IRB.getInt64(switch_id++);
  std::vector<Value *> args = {switch_cond_new, br_id};
  IRB.CreateCall(func, args);
  return true;
}

bool AFLCoverage::insertFunctionIndirectCall(Function *func, CallInst *CI) {
  IRBuilder<> IRB(CI);
  Value *targetValue = CI->getCalledValue();
  auto *br_id = IRB.getInt64(icall_id++);
  std::vector<Value *> args = {targetValue, br_id};
  IRB.CreateCall(func, args);
  return true;
}

bool AFLCoverage::insertFunctionIndirectCall(Function *func, InvokeInst *II) {
  IRBuilder<> IRB(II);
  Value *targetValue = II->getCalledValue();
  auto *br_id = IRB.getInt64(icall_id++);
  std::vector<Value *> args = {targetValue, br_id};
  IRB.CreateCall(func, args);
  return true;
}


bool AFLCoverage::insertFunctionStore(Function *func, StoreInst *SI) {
  IRBuilder<> IRB(SI);
  Value *store_address = SI->getPointerOperand();
  auto *w_id = IRB.getInt64(rw_id++);
  std::vector<Value *> args = {store_address, w_id};
  IRB.CreateCall(func, args);
  return true;
}

bool AFLCoverage::insertFunctionLoad(Function *func, LoadInst *LI) {
  IRBuilder<> IRB(LI);
  Value *load_address = LI->getPointerOperand();
  auto *r_id = IRB.getInt64(rw_id++);
  std::vector<Value *> args = {load_address, r_id};
  IRB.CreateCall(func, args);
  return true;
}

bool AFLCoverage::insertFunctionMemcpy(Function *func, CallInst *CI) {
  IRBuilder<> IRB(CI);
  Value *memcpy_dst = CI->getArgOperand(0);
  Value *memcpy_src = CI->getArgOperand(1);
  Value *memcpy_size = CI->getArgOperand(2);
  std::vector<Value *> args = {memcpy_dst, memcpy_src, memcpy_size};
  IRB.CreateCall(func, args);
  return true;
}

bool AFLCoverage::insertFunctionMemset(Function *func, CallInst *CI) {
  IRBuilder<> IRB(CI);
  Value *memset_dst = CI->getArgOperand(0);
  Value *memset_size = CI->getArgOperand(2);
  std::vector<Value *> args = {memset_dst, memset_size};
  IRB.CreateCall(func, args);
  return true;
}

static void registerAFLPass(const PassManagerBuilder &,
                            legacy::PassManagerBase &PM) {

  PM.add(new AFLCoverage());

}

static RegisterStandardPasses RegisterAFLPass(
    PassManagerBuilder::EP_ModuleOptimizerEarly, registerAFLPass);

static RegisterStandardPasses RegisterAFLPass0(
    PassManagerBuilder::EP_EnabledOnOptLevel0, registerAFLPass);
