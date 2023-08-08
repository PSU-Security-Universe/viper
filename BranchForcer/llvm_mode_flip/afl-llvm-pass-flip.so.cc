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

   This library is plugged into LLVM when invoking clang through afl-clang-fast.
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

      static char ID;
      AFLCoverage() : ModulePass(ID) { }
      bool runOnModule(Module &M) override;
      bool insertFunctionCondBr(Function *func, BranchInst *BI, ConstantInt *br_id);
  };

}

uint64_t branch_id = 0;

char AFLCoverage::ID = 0;

bool AFLCoverage::runOnModule(Module &M) {

  LLVMContext &C = M.getContext();

  IntegerType *Int1Ty = IntegerType::getInt1Ty(C);
  IntegerType *Int8Ty  = IntegerType::getInt8Ty(C);
  IntegerType *Int64Ty = IntegerType::getInt64Ty(C);
  PointerType *Ptr8Ty = PointerType::getInt8PtrTy(C);

  /* Show a banner */

  char be_quiet = 0;

  if (isatty(2) && !getenv("AFL_QUIET")) {

    SAYF(cCYA "afl-llvm-pass " cBRI VERSION cRST " by <lszekeres@google.com>\n");

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

  /* Int1Ty->return value, Int8Ty->original condition value, Int64Ty->branch */
  vector<Type *> args = {Int8Ty, Int64Ty, Ptr8Ty};
  auto *helpTy = FunctionType::get(Int1Ty, args, false);
  Function *flip_br_cond = dyn_cast<Function>(M.getOrInsertFunction("__flip_br_cond", helpTy));

  for (auto &F : M)
    for (auto &BB : F) {
      if (AFL_R(100) >= inst_ratio) continue;
      for (auto &I : BB) {
          if (isa<BranchInst>(I)) {
            BranchInst *BI = dyn_cast<BranchInst>(&I);
            /* Identify all conditional branch */
            if (BI->isConditional()) {
              inst_blocks++;
              IRBuilder<> IRB(BI);
              Value *br_cond = BI->getCondition();
              auto br_id = IRB.getInt64(branch_id++);
              LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
              MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
              Value *MapPtrIdx = IRB.CreateGEP(MapPtr, br_id);
              auto val = IRB.CreateAdd(IRB.CreateZExt(br_cond, Int8Ty), ConstantInt::get(Int8Ty, 1));
              auto pre_val = IRB.CreateLoad(MapPtrIdx);
              auto new_val = IRB.CreateOr(pre_val, val);
              StoreInst *SI = IRB.CreateStore(new_val, MapPtrIdx);
              SI->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
              this->insertFunctionCondBr(flip_br_cond, BI, br_id);
            }
          }
      }
    }


  /* Say something nice. */

  if (!be_quiet) {

    if (!inst_blocks) WARNF("No instrumentation targets found.");
    else OKF("Instrumented %u locations (%s mode, ratio %u%%).",
             inst_blocks, getenv("AFL_HARDEN") ? "hardened" :
             ((getenv("AFL_USE_ASAN") || getenv("AFL_USE_MSAN")) ?
              "ASAN/MSAN" : "non-hardened"), inst_ratio);

  }
  return true;

}

bool AFLCoverage::insertFunctionCondBr(Function *func, BranchInst *BI, ConstantInt *br_id) {
  IRBuilder<> IRB(&(*BI));
  const DILocation *DIB = BI->getDebugLoc();
  /* HY: Debug information of some conditional branch may be missing */
  if (DIB == NULL) {
    errs() << "Missing debug information\n";
    return true;
  }

  string debug_info = DIB->getDirectory().str() + "/" + DIB->getFilename().str() + ":" + to_string(DIB->getLine());
  Value *br_loc = IRB.CreateGlobalStringPtr(debug_info.c_str());
  Value *br_cond = BI->getCondition();
  vector<Value *> args = {br_cond, br_id, br_loc};
  /* Insert callsite of branch force function - flip_br_cond */
  Value *new_br_cond = IRB.CreateCall(func, args);
  BI->setCondition(new_br_cond);
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
