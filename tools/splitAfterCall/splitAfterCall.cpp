#include "splitAfterCall.h"
#include <cstdio>

#define endl "\n"

using namespace llvm;

static cl::opt<bool> removeDeadFuncKnob("removeDeadFunc", cl::init(false),
    cl::desc("remove dead functions, use this only you are sure"));

char splitAfterCall::ID = 0;

void splitAfterCall::splitIt(Module &M) {

  std::vector<BasicBlock *> AllBBs;
  std::vector<BasicBlock *>::iterator iter, end;

  for (auto &F : M)
    for (auto &BB : F)
      AllBBs.push_back(&BB);

  for (iter = AllBBs.begin(), end = AllBBs.end(); iter != end; iter++) {

    BasicBlock * BB = *iter;

    BasicBlock::iterator b_iter, b_end;

    b_iter = BB->begin();
    b_end = BB->end();

    bool to_split = false;

    for (; b_iter != b_end; ) {

      if (to_split) {

        BasicBlock * newBB = BB->splitBasicBlock(b_iter);

        b_iter = newBB->begin();
        b_end = newBB->end();
        BB = newBB;
      }

      Instruction * I = &(*b_iter++);

      if (!isa<CallInst>(I)) 
        to_split = false;
      else                   
        to_split = true;
    }

  }
}

bool splitAfterCall::runOnModule(Module &M) {

  splitIt(M);

  return false;
}

static RegisterPass<splitAfterCall> X("splitAfterCall", "encoding IR debug info to file");

static void registersplitAfterCallPass(const PassManagerBuilder &,
    legacy::PassManagerBase &PM) {
  PM.add(new splitAfterCall());
}

static RegisterStandardPasses RegistersplitAfterCallPass(
    PassManagerBuilder::EP_OptimizerLast, registersplitAfterCallPass);
    //PassManagerBuilder::EP_EarlyAsPossible, registersplitAfterCallPass);
    //PassManagerBuilder::EP_ModuleOptimizerEarly, registersplitAfterCallPass);
static RegisterStandardPasses RegistersplitAfterCallPass0(
    PassManagerBuilder::EP_EnabledOnOptLevel0, registersplitAfterCallPass);
