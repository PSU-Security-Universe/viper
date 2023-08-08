# splitAfterCall


## Build

```bash
cd splitAfterCall
make
```

## Usage 


use the following command once we extracted the bitcode file of target program.

```bash
clang -Xclang -load -Xclang /path/to/splitAfterCall.so old.bc -emit-llvm -c -o new.bc
```

for example: 

```
extract-bc sqlite3
clang -Xclang -load -Xclang /path/to/splitAfterCall.so sqlite3.bc -emit-llvm -c -o sqlite3_splitted.bc
```
