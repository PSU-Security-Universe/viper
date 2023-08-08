cmake_minimum_required(VERSION 3.13.4)
project(SimpleProject)

find_package(LLVM REQUIRED CONFIG)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

# Set your project compile flags.
# E.g. if using the C++ header files
# you will need to enable C++11 support
# for your compiler.
include_directories(${LLVM_INCLUDE_DIRS})
separate_arguments(LLVM_DEFINITIONS_LIST NATIVE_COMMAND ${LLVM_DEFINITIONS})
add_definitions(${LLVM_DEFINITIONS_LIST})

# add_compile_options(-fsanitize=address -g -O0 -gdwarf-2)
# add_link_options(-fsanitize=address -g -O0 -gdwarf-2)

# Now build our tools
add_executable(rator rator.cpp)
add_executable(rator_arg rator_arg.cpp)

# Find the libraries that correspond to the LLVM components
# that we wish to use
llvm_map_components_to_libnames(llvm_libs support core irreader)

# Link against LLVM libraries
target_link_libraries(rator ${llvm_libs})
target_link_libraries(rator_arg ${llvm_libs})
