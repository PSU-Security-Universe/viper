#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/TargetFolder.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/IR/CallSite.h"
#include "llvm/Support/Format.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/CFG.h"
#include "llvm/Support/Compiler.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/Support/CommandLine.h"

using namespace llvm;

namespace {

  class splitAfterCall : public ModulePass {

    public:
      static char ID;
      splitAfterCall() : ModulePass(ID) { }

      void splitIt(Module &M);

      bool runOnModule(Module &M) override;
  };
}

