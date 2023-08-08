#!/bin/bash

git clone https://github.com/sqlite/sqlite.git
cd sqlite
git checkout version-3.40.1
export CC=wllvm CXX=wllvm++ LLVM_COMPILER=clang CFLAGS="-g -O0" CXXFLAGS="-g -O0"
./configure 
make