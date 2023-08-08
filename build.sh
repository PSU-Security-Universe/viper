#!/bin/bash

make -C BranchForcer
make -C BranchForcer/llvm_mode_flip
make -C BranchForcer/llvm_mode_rate
make -C tools/splitAfterCall

cmake -B ./VariableRator/build VariableRator
cmake --build ./VariableRator/build