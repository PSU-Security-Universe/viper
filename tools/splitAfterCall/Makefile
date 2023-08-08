CXX = clang
LLVM_CONFIG ?= llvm-config
CLANG_CFL    = `$(LLVM_CONFIG) --cxxflags` -fno-rtti -fpic $(CXXFLAGS) -g -O0
CLANG_LFL    = `$(LLVM_CONFIG) --ldflags` $(LDFLAGS) -Wl,-znodelete -g

all: splitAfterCall.so

splitAfterCall.so: splitAfterCall.cpp splitAfterCall.h
	$(CXX) $(CLANG_CFL) -shared $< -o $@ $(CLANG_LFL)

clean:
	rm splitAfterCall.so
