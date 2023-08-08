#!/bin/bash

mkdir $2/log
mkdir $2/dot

cp $1/tools/rec_ori_files.py $2
cp $1/tools/rm_gen_files.py $2
cp $1/tools/libcall $2/log/
cp $1/tools/lib_func_map_gen.py $2
cp $1/tools/auto_rator.py $2
cp $1/VariableRator/build/rator $2
cp $1/VariableRator/build/rator_arg $2
