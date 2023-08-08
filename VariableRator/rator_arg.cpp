#include <cstdint>
#include <deque>
#include <fstream>
#include <iostream>
#include <map>
#include <llvm/IR/Instruction.h>
#include <llvm/Support/Casting.h>
#include <sstream>
#include <string>
#include <vector>

#include <stdio.h>
#include <stdlib.h>
#include <sys/stat.h>
#include <unistd.h>

#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Pass.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/raw_ostream.h"

#define LOG_CACHE_SIZE (100)
#define BB_ARRAY_SIZE (1024 * 1024 * 16)

#define TRACE_LOG_FILE "./log/trace_log"
#define VAL_LOG_FILE "./log/val_log"
#define RW_LOG_FILE "./log/store_load_log"
#define FUNC_MAP_FILE "./log/func_map"
#define LIB_FUNC_MAP_FILE "./log/lib_func_map"
#define PROC_MAP_FILE "./log/proc_map"
#define LIBCALL_FILE "./log/libcall"
#define BR_LOG_FILE "./log/br_log"
#define BITS_MASK 0x0000ffffffffffff

/* Two Debug Levels */
#define BR_DEBUG 1
#define RW_DEBUG 1
#define ENABLE_VALIDATE 0
#define VAL_DEBUG 0

using namespace llvm;
using namespace std;

typedef unsigned char u8;
typedef unsigned int u32;
typedef unsigned long u64;
typedef signed int s32;
typedef signed long s64;

typedef struct {
  BasicBlock *BB_ptr;
  vector<u64> rw_vector; // 按顺序存储一个BasicBlock中的store/load/memcpy操作
  map<Instruction *, u64>
      indirect_call_addr_map; // 存储每个BB中indirect call指令对应的地址
} BB_info;

typedef struct {
  Value *op;
  u32 index;
  u32 node_id = 0;
  u32 location = 0; // 1 -> global, 2 -> heap, 3 -> stack, 0 -> not a ptr
  u32 store_dist =
      0; // how many store instructions exist between load and store?
} op_info;

class DFTreeNode {
public:
  op_info data;
  DFTreeNode *left;
  DFTreeNode *right;
  DFTreeNode(op_info new_op) {
    data = new_op;
    left = NULL;
    right = NULL;
  }
};

FILE *trace_log = NULL;
u8 *trace_log_cache = NULL;
u32 byte_index = 0;
u32 file_size = 0;
u32 load_time = 0;

FILE *val_log = NULL;
u8 *val_log_cache = NULL;
u32 val_byte_index = 0;
u32 val_file_size = 0;
u32 val_load_time = 0;

FILE *rw_log = NULL;
FILE *br_log = NULL;

vector<BB_info> BB_array;
u32 BB_array_index = 0;

u32 start_index = 0;
u32 num_BB_print = 0;
u32 cond_br_counter = 0;
u32 cond_br_num;
string cond_br_id;
string dot_path;
string graph_folder_path;
string syscall_name;
string libcall_name;
// BasicBlock *target_BB = nullptr;

uint32_t memcpyOffset = 0;

map<u64, string> func_map;
/* map indirect callsite address and function name during replaying.
When encounter a indirect call during analysis, check the callsite_map
to find corresponding function name */
map<Instruction *, string> callsite_map;
multimap<string, string> libcall_map;
map<string, vector<int>> libcall_arg;
vector<string> libcall_vec;
map<Instruction *, u64> rw_map;
map<Instruction *, u64> br_map;
map<u64, Instruction *> rw_map_rev;
map<u64, Instruction *> br_map_rev;

BasicBlock *setjmp_BB = nullptr;
Instruction *setjmp_I = nullptr;
Function *setjmp_F = nullptr;
bool longjmp_ret = false;
bool setjmp_next = false;

u32 location_rep = 4;
u32 store_dist_global = 0;
u32 store_dist_heap = 0;
u32 store_dist_stack = 0;

u32 store_dist_global_sum = 0;
u32 store_dist_heap_sum = 0;
u32 store_dist_stack_sum = 0;

u64 global_range[2];
u64 heap_range[2];
u64 stack_range[2];

u32 score = 0;
u64 record_count = 0;
u64 store_load_count = 0;
u64 br_id_count = 0;
BranchInst *last_br = nullptr;
StoreInst *last_store = nullptr;
LoadInst *last_load = nullptr;
CallInst *last_call = nullptr;

bool exit_flag = false;
bool end_traverse = false;

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

namespace {
class Rator : public ModulePass {
public:
  static char ID;
  Rator() : ModulePass(ID) {}
  bool runOnModule(Module &M) override;
  void traverseFunc(Function *F);
  BasicBlock *traverseBB(BasicBlock *BB);
};
} // namespace

char Rator::ID = 0;

void func_map_gen() {

  if (access(FUNC_MAP_FILE, F_OK) != 0 || 
    access(LIB_FUNC_MAP_FILE, F_OK) != 0) {
    errs() << "Not found func_map or lib_func_map\n";
    exit(1);
  }

  ifstream func_map_file(FUNC_MAP_FILE);
  if (func_map_file.is_open()) {
    string line;
    while (getline(func_map_file, line)) {
      string address = line.substr(0, 16);
      string function_name;
      s32 pos_1 = line.find("@plt");
      s32 pos_2 = line.find(">:");
      if (pos_1 != -1) {
        function_name = line.substr(18, pos_1 - 18);
      } else {
        function_name = line.substr(18, pos_2 - 18);
      }
      stringstream temp;
      u64 address_int;
      temp << address;
      temp >> hex >> address_int;
      func_map[address_int] = function_name;
    }
    func_map_file.close();
  }


  ifstream lib_func_map_file(LIB_FUNC_MAP_FILE);
  if (lib_func_map_file.is_open()) {
    string line;
    while (getline(lib_func_map_file, line)) {
      s64 pos = line.find(" ");
      u64 address_int = stol(line.substr(0, pos));
      func_map[address_int] = line.substr(pos + 1);
    }
    lib_func_map_file.close();
  }
}

vector<string> string_splitter(string &s, char delimiter) {
  size_t start = 0;
  size_t end = s.find_first_of(delimiter);

  vector<string> output;
  while (end <= string::npos) {
    output.emplace_back(s.substr(start, end - start));

    if (end == string::npos)
      break;

    start = end + 1;
    end = s.find_first_of(delimiter, start);
  }

  return output;
}


void libcall_map_gen() {
  if (access(LIBCALL_FILE, F_OK)) {
    // libcall not exists, exit. 
    errs() << "[x] Not found libcall, please place it to " << LIBCALL_FILE << "\n";
    exit(1);
  }

  ifstream libcall_file(LIBCALL_FILE);
  if (libcall_file.is_open()) {

    string line;
    while (getline(libcall_file, line)) {
      vector<string> functions =  string_splitter(line, ':');

      // Use first element as syscall
      string syscall = functions[0];

      for (int i=1; i<functions.size();i++) {
        string funcNameWithArgs = functions[i];
        vector<string> funcWithArgs = string_splitter(funcNameWithArgs, '@');

        // Use first element as function name
        string function = funcWithArgs[0];
        libcall_map.insert(make_pair(syscall, function));

        // errs() << "syscall: " << syscall   << " "
        //        << "function: " << function <<"\n";

        for (int j=1; j<funcWithArgs.size();j++) {
          size_t argIdx = stoi(funcWithArgs[j]);
          libcall_arg[function].push_back(argIdx);

          // errs() << "function: " << function   << " "
          //       << "argument: " << argIdx <<"\n";
        }
      }
    }
  }
}

void procAddrStrToInt(string line, u64 &lower_bound_int,
                      u64 &higher_bound_int) {
  u32 addr_length = line.find_first_of("-");
  stringstream temp;
  temp << line.substr(0, addr_length);
  temp >> hex >> lower_bound_int;
  temp.clear();
  temp << line.substr(addr_length + 1, addr_length);
  temp >> hex >> higher_bound_int;
}

void proc_map_gen() {
  ifstream proc_map_file(PROC_MAP_FILE);
  if (proc_map_file.is_open()) {
    string line;
    u64 lower_bound_int;
    u64 higher_bound_int;
    getline(proc_map_file, line);
    procAddrStrToInt(line, lower_bound_int, higher_bound_int);
    global_range[0] = lower_bound_int;
    global_range[1] = higher_bound_int;

    while (getline(proc_map_file, line)) {
      procAddrStrToInt(line, lower_bound_int, higher_bound_int);
      if (lower_bound_int == global_range[1]) {
        global_range[1] = higher_bound_int;
      } else if (line.find("_record") != string::npos) {
        // NOTE: recognize `global_range` using name pattern.
        global_range[1] = higher_bound_int;
      }

      if (line.find("[stack]") != string::npos) {
        stack_range[0] = lower_bound_int;
        stack_range[1] = higher_bound_int;
      }
    }
    heap_range[0] = global_range[1] + 1;
    heap_range[1] = stack_range[0] - 1;
    proc_map_file.close();
  }
}

/* Load data from trace_data.log or val_data.log */
void loadData(FILE *file, u8 *log_cache, u32 file_size, u32 &load_time,
              u32 &byte_index) {
  u32 remaining_size = file_size - load_time * LOG_CACHE_SIZE;
  load_time++;
  if (remaining_size > LOG_CACHE_SIZE) {
    memset(log_cache, 0, LOG_CACHE_SIZE);
    if (fread(log_cache, 1, LOG_CACHE_SIZE, file) != LOG_CACHE_SIZE) {
      errs() << "failed to read log cache, exit.\n";
      exit(1);
    }
    byte_index = 0;
  } else {
    memset(log_cache, 0, LOG_CACHE_SIZE);
    if (fread(log_cache, 1, remaining_size, file) != remaining_size) {
      errs() << "failed to read remaining log cache, exit.\n";
      exit(1);
    }
    fclose(file);
    byte_index = 0;
  }
}


u8 read_u8_from_file(FILE* file) {
  u8 data = 0;
  size_t size_in_bytes = sizeof(data);
  if (fread(&data, size_in_bytes, 1, file) != 1) {
    errs() << "failed to read u8 from file, exit.\n";
    exit(1);
  }
  return data;
}

u32 read_u32_from_file(FILE* file) {
  u32 data = 0;
  size_t size_in_bytes = sizeof(data);
  if (fread(&data, size_in_bytes, 1, file) != 1) {
    errs() << "failed to read u32 from file, exit.\n";
    exit(1);
  }
  return data;
}

u64 read_u64_from_file(FILE* file) {
  u64 data = 0;
  size_t size_in_bytes = sizeof(data);
  if (fread(&data, size_in_bytes, 1, file) != 1) {
    errs() << "failed to read u64 from file, exit.\n";
    exit(1);
  }
  return data;
}


u8 getValByte(u8 *val_log_cache) {
  if (val_byte_index == LOG_CACHE_SIZE) {
    loadData(val_log, val_log_cache, val_file_size, val_load_time,
             val_byte_index);
  }

  u8 temp = val_log_cache[val_byte_index++];

#if VAL_DEBUG==1
  errs() << "val_log: " << int(temp) << "\n";
#endif

  return temp;
}


u8 getBrCond() {
  return read_u8_from_file(trace_log);
}


u32 getSwitchCond() {
  // get switch condition from trace log
  u32 switch_cond_int = read_u32_from_file(trace_log);
  return switch_cond_int;
}


u64 getIndirectCallAddr() {
  // get indirect call address from trace log
  u64 address_int_sec = read_u64_from_file(trace_log);
  return address_int_sec;
}

void recordBB(BasicBlock *BB) {
  BB_array[BB_array_index].BB_ptr = BB;
  BB_array_index++;
}

void printBB(u32 index, u32 num) {
  if (num > (index + 1)) {
    fprintf(stderr, "Don't have enough BBs to print\n");
  } else {
    while (num--) {
      errs() << "label: ";
      BB_array[index].BB_ptr->printAsOperand(errs(), false);
      errs() << "\n";
      errs() << BB_array[index].BB_ptr->getParent()->getName() << "\n";
      for (auto &I : *BB_array[index].BB_ptr)
        errs() << I << "\n";
      errs() << "-------------------------\n";
      index--;
    }
  }
}

/* Return the index of the target BB */
u32 locateBB(u32 index, BasicBlock *BB_target) {
  BasicBlock *BB_current = BB_array[index].BB_ptr;
  while (BB_current != BB_target) {
    BB_current = BB_array[--index].BB_ptr;
  }
  return index;
}

op_info saveOpInfo(Value *op, u32 index) {
  op_info new_op;
  if (isa<GlobalVariable>(op)) {
    new_op = {op, index};
  } else if (isa<Argument>(op)) {
    new_op = {op, index};
  } else if (isa<Constant>(op)) {
    new_op = {op, index};
  } else if (BasicBlock *BB_target = dyn_cast<Instruction>(op)->getParent()) {
    index = locateBB(index, BB_target);
    new_op = {op, index};
  }
  return new_op;
}

bool traverseDFT(DFTreeNode *root, vector<DFTreeNode *> &op_vec) {
  op_vec.push_back(root);
  if (root == nullptr) {
    op_vec.pop_back();
    return false;
  }
  bool ret_left = traverseDFT(root->left, op_vec);
  bool ret_right = traverseDFT(root->right, op_vec);
  op_vec.pop_back();
  return true;
}

void assignNodeId(DFTreeNode *root, u32 &node_id) {
  if (root == nullptr) {
    node_id++;
    return;
  }
  root->data.node_id = node_id;
  node_id++;
  assignNodeId(root->left, node_id);
  assignNodeId(root->right, node_id);
  return;
}

string valueToString(Value *val) {
  string str;
  raw_string_ostream stream(str);
  stream << *val;
  str = stream.str();
  return str;
}

void createDot(DFTreeNode *root, ofstream &fout) {
  if (root == nullptr) {
    return;
  }
  string color_str;
  string location_str;
  if (dyn_cast<LoadInst>(root->data.op)) {
    if (root->data.location == 1 || (root->data.store_dist >= 100)) {
      color_str = "red";
    } else if ((root->data.location == 2) || (root->data.store_dist >= 50)) {
      color_str = "yellow";
    } else if ((root->data.location == 3) || (root->data.store_dist < 50)) {
      color_str = "green";
    }
    fout << root->data.node_id << ":body[style=filled color=" << color_str
         << "]\n";
    switch (root->data.location) {
    case 1:
      location_str = "Global";
      location_rep = 1;
      store_dist_global = (store_dist_global > root->data.store_dist)
                              ? store_dist_global
                              : root->data.store_dist;
      store_dist_global_sum += root->data.store_dist;           
      break;
    case 2:
      location_str = "Heap";
      location_rep = (location_rep > 2) ? 2 : location_rep;
      store_dist_heap = (store_dist_heap > root->data.store_dist)
                            ? store_dist_heap
                            : root->data.store_dist;
      store_dist_heap_sum += root->data.store_dist;           
      break;
    case 3:
      location_str = "Stack";
      location_rep = (location_rep > 3) ? 3 : location_rep;
      store_dist_stack = (store_dist_stack > root->data.store_dist)
                             ? store_dist_stack
                             : root->data.store_dist;
      store_dist_stack_sum += root->data.store_dist;           
      break;
    default:
      location_str = "Not Found";
      break;
    }
  }
  //去掉特殊字符，否则dot打印不出来图片
  string inst_str = valueToString(root->data.op);
  inst_str.erase(remove(inst_str.begin(), inst_str.end(), '\"'),
                 inst_str.end());

  fout << root->data.node_id << "[shape=rectangle,label="
       << "\"" << inst_str << "\""
       << "];\n";
  // fout << root->data.node_id << ":body[style=filled color=lightblue]\n";

  if (root->left) {
    if (dyn_cast<LoadInst>(root->data.op)) {
      fout << root->data.node_id << " -> " << root->left->data.node_id
           << " [label = \"" << location_str
           << ", store distance:" << root->data.store_dist << "\"];\n";
      score += root->data.store_dist;
    } else {
      fout << root->data.node_id << " -> " << root->left->data.node_id << "\n";
    }
  }
  if (root->right) {
    if (dyn_cast<LoadInst>(root->data.op)) {
      fout << root->data.node_id << " -> " << root->right->data.node_id
           << " [label = \"" << location_str
           << ", store distance: " << root->data.store_dist << "\"]\n";
      score += root->data.store_dist;
    } else {
      fout << root->data.node_id << " -> " << root->right->data.node_id << "\n";
    }
  }
  createDot(root->left, fout);
  createDot(root->right, fout);
  return;
}

void drawDFT(DFTreeNode *root) {
  ofstream fout;
  string location_rep_str;
  u32 node_id = 0;
  assignNodeId(root, node_id);
  errs() << dot_path << "\n";
  fout.open(dot_path);
  if (!fout)
    cout << "open file failed!" << endl;
  fout << "digraph {\n";
  createDot(root, fout);

  switch (location_rep) {
  case 1:
    location_rep_str = "Global";
    break;
  case 2:
    location_rep_str = "Heap";
    break;
  case 3:
    location_rep_str = "Stack";
    break;
  case 4:
    location_rep_str = "None";
    break;
  }

  fout << to_string(node_id) << "[shape=rectangle,label=\"" << location_rep_str
       << ",GD:" << to_string(store_dist_global)
       << ",HD:" << to_string(store_dist_heap)
       << ",SD:" << to_string(store_dist_stack) << "\"]\n";

  fout << to_string(node_id) << "[shape=rectangle,label=\"" << location_rep_str
       << ",GlobalSum:" << to_string(store_dist_global_sum)
       << ",HeapSum:" << to_string(store_dist_heap_sum)
       << ",StackSum:" << to_string(store_dist_stack_sum) << "\"]\n";

  fout << "}";
  fout.close();
}

u32 getLoadIndex(LoadInst *LI_target, u32 index) {
  u32 load_index = 0;
  for (auto &I : *(BB_array[index].BB_ptr)) {
    if (StoreInst *StI = dyn_cast<StoreInst>(&I)) {
      load_index++;
    } else if (CallInst *CI = dyn_cast<CallInst>(&I)) {
      if (CI->getCalledFunction() != nullptr) {
        if (CI->getCalledFunction()->getName() == "llvm.memcpy.p0i8.p0i8.i64") {
          load_index = load_index + 3;
        } else if (CI->getCalledFunction()->getName() ==
                   "llvm.memset.p0i8.i64") {
          load_index = load_index + 2;
        }
      }
    } else if (LoadInst *LI = dyn_cast<LoadInst>(&I)) {
      if (LI == LI_target) {
        return load_index;
      } else {
        load_index++;
      }
    }
  }
}

Value *findMatchedStore(u32 load_index, u32 &index_cur, u32 &store_dist) {
  //在同一个BB，从当前load_index倒序
  //不在同一个BB，从最后一条倒序
  u32 store_index;
  u64 load_op_id = BB_array[index_cur].rw_vector[load_index] & BITS_MASK;
  load_op_id += memcpyOffset;
  u64 store_op_id;
  BasicBlock *orig_BB =
      BB_array[index_cur].BB_ptr; //用于判断是否与targe load在一个BB中
  Instruction *I = nullptr; //将iterator转换成insturction *方便操作
  Function *orig_Func = orig_BB->getParent();
  bool valid_match_flag = false; //只有当valid_match_flag为true才视作有效match
  bool dist_record_flag = true; //只有当dis_record_flag为true才开始计数
  bool before_call_flag = true;
  while (index_cur != 0xffffffff) {
    for (auto &I : *(BB_array)[index_cur].BB_ptr) {
      if (CallInst *CI = dyn_cast<CallInst>(&I)) {
        if (CI->getCalledFunction() != nullptr) {
          if (CI->getCalledFunction()->getName() == orig_Func->getName()) {
            before_call_flag = false;
          }
        }
      }
    }

    store_index = BB_array[index_cur].rw_vector.size() - 1;
    for (BasicBlock::reverse_iterator i = BB_array[index_cur].BB_ptr->rbegin(),
                                      e = BB_array[index_cur].BB_ptr->rend();
         i != e; ++i) {
      I = &(*i);
      // if((BB_array[index_cur].BB_ptr == orig_BB) && (store_index ==
      // load_index)) {
      //     dist_record_flag = true;
      // }
      if ((BB_array[index_cur].BB_ptr != orig_BB) ||
          (store_index < load_index)) {
        valid_match_flag = true;
      }

      if (before_call_flag == false) {
        valid_match_flag = false;
      }

      if (StoreInst *StI = dyn_cast<StoreInst>(I)) {
        store_op_id = BB_array[index_cur].rw_vector[store_index] & BITS_MASK;
        // errs() << store_index << "\n";
        // errs() << store_op_id << "\n";
        // errs() << load_op_id << "\n";
        if ((store_op_id == load_op_id) && valid_match_flag) {
          memcpyOffset = 0;
          return dyn_cast<Value>(StI);
        } else {
          if (dist_record_flag)
            store_dist++;
          store_index--;
        }
      } else if (CallInst *CI = dyn_cast<CallInst>(I)) {
        if (CI->getCalledFunction() != nullptr) {
          u64 store_src_id;
          u64 store_dst_id;
          u64 store_size; // third argument in memset
          if (CI->getCalledFunction()->getName() ==
              "llvm.memcpy.p0i8.p0i8.i64") {
            store_size =
                BB_array[index_cur].rw_vector[store_index] & BITS_MASK;
            store_src_id =
                BB_array[index_cur].rw_vector[store_index - 1] & BITS_MASK;
            store_dst_id =
                BB_array[index_cur].rw_vector[store_index - 2] & BITS_MASK;

            if ((store_dst_id <= load_op_id &&
                load_op_id <= (store_dst_id + 8* (store_size - 1))) && 
                valid_match_flag) {

              memcpyOffset = load_op_id - store_dst_id;

              // errs() << "to find load addr: " << load_op_id << "\n";
              // errs() << "memcpy(" << store_dst_id << ", "
              //        << store_src_id << ", " << store_size << ");\n";
              // errs() << "find new load:     " << memcpyOffset + store_src_id << "\n";
              // errs() << "memcpyOffset: " << memcpyOffset << "\n";
              // errs() << "CallInst: " << *CI << "\n\n\n";

              return findMatchedStore(store_index-1, index_cur, store_dist);
              // return CI->getArgOperand(1); //不return 直接找memcpy
            } else {
              store_index = store_index - 3;
            }
          } else if (CI->getCalledFunction()->getName() ==
                     "llvm.memset.p0i8.i64") {
            store_size = BB_array[index_cur].rw_vector[store_index] & BITS_MASK;
            store_dst_id =
                BB_array[index_cur].rw_vector[store_index - 1] & BITS_MASK;
            if ((store_dst_id <= load_op_id) &&
                (load_op_id <= (store_dst_id + 8 * (store_size - 1))) &&
                valid_match_flag) {
              // errs() << CI->getArgOperand(1);
              // return CI->getArgOperand(1);
              return dyn_cast<Value>(CI);
            } else {
              store_index = store_index - 2;
            }
          } else if (CI->getCalledFunction()->getName() ==
                     orig_Func->getName()) {
            before_call_flag = true;
          }
        }
      } else if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
        store_index--;
      }
    }
    index_cur--;
  }
  return nullptr;
}

Value *findMatchedCallSite(Function *func_target, bool &call_flag,
                           u32 &index_cur) {
  index_cur--;
  while (index_cur) {
    for (auto &I : *(BB_array[index_cur].BB_ptr)) {
      if (CallInst *CI = dyn_cast<CallInst>(&I)) {
        if (CI->getCalledFunction() == nullptr) {
          auto iter = BB_array[index_cur].indirect_call_addr_map.find(CI);
          if (iter != BB_array[index_cur].indirect_call_addr_map.end()) {
            auto iter_2 = func_map.find(iter->second);
            if (iter_2 != func_map.end()) {
              if (iter_2->second == func_target->getName()) {
                call_flag = true;
              }
            }
          }
          return dyn_cast<Value>(CI);
        } else if (CI->getCalledFunction() == func_target) {
          call_flag = true;
          return dyn_cast<Value>(CI);
        }
      }
      if (InvokeInst *II = dyn_cast<InvokeInst>(&I)) {
        if (II->getCalledFunction() == nullptr) {
          auto iter = BB_array[index_cur].indirect_call_addr_map.find(II);
          if (iter != BB_array[index_cur].indirect_call_addr_map.end()) {
            auto iter_2 = func_map.find(iter->second);
            if (iter_2 != func_map.end()) {
              if (iter_2->second == func_target->getName()) {
                call_flag = true;
              }
            }
          }
          return dyn_cast<Value>(II);
        } else if (II->getCalledFunction() == func_target) {
          call_flag = true;
          return dyn_cast<Value>(II);
        }
      }
    }
    index_cur--;
  }
  return nullptr;
}

Value *findMatchedRet(Function *func_target, u32 &index_cur) {
  // 因为callsite对应函数的basicblock一定在callsite的后面，向后查找matched
  // return
  index_cur++;
  while (index_cur < BB_array_index) {
    for (auto &I : *(BB_array)[index_cur].BB_ptr) {
      if (ReturnInst *RI = dyn_cast<ReturnInst>(&I)) {
        if (RI->getFunction() == func_target) {
          return dyn_cast<Value>(RI);
        }
      }
    }
    index_cur++;
  }
  return nullptr;
}

void dataflowAnalysis(u32 index, Value *cond) {
  BasicBlock *BB_start = BB_array[index].BB_ptr;
  deque<DFTreeNode *> op_deque;

  op_info start_op = saveOpInfo(cond, index);
  DFTreeNode *root = new DFTreeNode(start_op);
  op_deque.push_front(root);
  vector<DFTreeNode *> op_vec; // used for traversing the BST
  /* op_deque有两种callsite, 一种是callinst的返回值在dataflow中,
   * 需要进入函数中继续分析，
   * 另一种是当前operand来自函数的某个参数，我们不需要进入函数，只需要找到callsite中对应参数即可，但是为了增强trace的可读性，仍然将callsite加入BST中，只是用于打印，不进行额外操作。
   * call_flag == false 代表第一种，call_flag == true 代表第二种 */
  bool call_flag = false;
  Argument *op_arg = NULL;
  while (op_deque.size()) {
    DFTreeNode *DFTreeNode_cur = op_deque[0];
    DFTreeNode *DFTreeNode_left = NULL;
    DFTreeNode *DFTreeNode_right = NULL;
    Value *op_left = NULL;
    Value *op_right = NULL;
    u32 index_cur = DFTreeNode_cur->data.index;
    Value *op_cur = DFTreeNode_cur->data.op;
    //errs() << *op_cur << "\n";
    if (isa<Constant>(op_cur)) {
      op_deque.pop_front();
      continue;
    }
    if (isa<GlobalVariable>(op_cur)) {
      op_deque.pop_front();
      continue;
    }
    if (isa<Argument>(op_cur)) {
      op_arg = dyn_cast<Argument>(op_cur);
      op_deque.pop_front();
      op_left = findMatchedCallSite(op_arg->getParent(), call_flag, index_cur);

      if (op_left != nullptr) {
        DFTreeNode_cur->left = new DFTreeNode(saveOpInfo(op_left, index_cur));
        op_deque.push_front(DFTreeNode_cur->left);
      }
      continue;
    }

    Instruction *inst_cur = dyn_cast<Instruction>(op_cur);
    // errs() << *inst_cur << "\n";
    if (ICmpInst *II = dyn_cast<ICmpInst>(inst_cur)) {
      op_deque.pop_front();
      op_left = II->getOperand(0);
      op_right = II->getOperand(1);
      // if (!isa<Constant>(op_left)) {
      // errs() << *op_left << "\n";
      DFTreeNode_cur->left = new DFTreeNode(saveOpInfo(op_left, index_cur));
      op_deque.push_front(DFTreeNode_cur->left);
      //}
      // if (!isa<Constant>(op_right)) {
      // errs() << *op_right << "\n";
      DFTreeNode_cur->right = new DFTreeNode(saveOpInfo(op_right, index_cur));
      op_deque.push_front(DFTreeNode_cur->right);
      //}
      continue;
    }

    else if (BinaryOperator *BO = dyn_cast<BinaryOperator>(inst_cur)) {
      op_deque.pop_front();
      op_left = BO->getOperand(0);
      op_right = BO->getOperand(1);
      // if (!isa<Constant>(op_left)) {
      // errs() << *op_left << "\n";
      DFTreeNode_cur->left = new DFTreeNode(saveOpInfo(op_left, index_cur));
      op_deque.push_front(DFTreeNode_cur->left);
      //}
      // if (!isa<Constant>(op_right)) {
      // errs() << *op_right << "\n";
      DFTreeNode_cur->right = new DFTreeNode(saveOpInfo(op_right, index_cur));
      op_deque.push_front(DFTreeNode_cur->right);
      //}
      continue;
    }

    else if (isa<SExtInst>(inst_cur) || isa<ZExtInst>(inst_cur) ||
             isa<TruncInst>(inst_cur) || isa<PtrToIntInst>(inst_cur) ||
             isa<IntToPtrInst>(inst_cur)) {
      op_deque.pop_front();
      op_left = inst_cur->getOperand(0);
      // if (!isa<Constant>(op_left)) {
      // errs() << *op_left << "\n";
      DFTreeNode_cur->left = new DFTreeNode(saveOpInfo(op_left, index_cur));
      op_deque.push_front(DFTreeNode_cur->left);
      //}
      continue;
    }

    else if (LoadInst *LI = dyn_cast<LoadInst>(inst_cur)) {
      op_deque.pop_front();
      u32 load_index = getLoadIndex(LI, index_cur);
      u64 load_op_id = BB_array[index_cur].rw_vector[load_index] & BITS_MASK;
      u32 load_location = 0;
      u32 store_dist = 0;
      if ((global_range[0] <= load_op_id) && (load_op_id <= global_range[1])) {
        load_location = 1;
      } else if ((heap_range[0] <= load_op_id) &&
                 (load_op_id <= heap_range[1])) {
        load_location = 2;
      } else if ((stack_range[0] <= load_op_id) &&
                 (load_op_id <= stack_range[1])) {
        load_location = 3;
      }
      DFTreeNode_cur->data.location = load_location;
      op_left = findMatchedStore(load_index, index_cur, store_dist);
      DFTreeNode_cur->data.store_dist = store_dist;
      if (op_left != nullptr) {
        DFTreeNode_cur->left = new DFTreeNode(saveOpInfo(op_left, index_cur));
        op_deque.push_front(DFTreeNode_cur->left);
      }
      continue;
    }

    else if (StoreInst *StI = dyn_cast<StoreInst>(inst_cur)) {
      op_deque.pop_front();
      // op_left = inst_cur->getOperand(0);
      op_left = StI->getValueOperand();
      // if (!isa<Constant>(op_left)) {
      DFTreeNode_cur->left = new DFTreeNode(saveOpInfo(op_left, index_cur));
      op_deque.push_front(DFTreeNode_cur->left);
      //}
      continue;
    }

    else if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(inst_cur)) {
      op_deque.pop_front();
      // need to figure out higher level api --> getOperand()
      op_left = GEP->getPointerOperand();
      // if (!isa<Constant>(op_left)) {
      // errs() << *op_left << "\n";
      DFTreeNode_cur->left = new DFTreeNode(saveOpInfo(op_left, index_cur));
      op_deque.push_front(DFTreeNode_cur->left);
      //}
      continue;
    }

    else if (PHINode *PN = dyn_cast<PHINode>(inst_cur)) {
      op_deque.pop_front();
      BasicBlock *BB_current = BB_array[index_cur].BB_ptr;
      BasicBlock *BB_income = BB_array[--index_cur].BB_ptr;
      while ((BB_income->getParent() != inst_cur->getFunction())) {
        BB_income = BB_array[--index_cur].BB_ptr;
      }
      op_left = PN->getIncomingValueForBlock(BB_income);
      DFTreeNode_cur->left = new DFTreeNode(saveOpInfo(op_left, index_cur));
      op_deque.push_front(DFTreeNode_cur->left);
      continue;
    }

    else if (CallInst *CI = dyn_cast<CallInst>(inst_cur)) {
      if (call_flag) {
        op_deque.pop_front();
        op_left = CI->getArgOperand(op_arg->getArgNo());
        DFTreeNode_cur->left = new DFTreeNode(saveOpInfo(op_left, index_cur));
        op_deque.push_front(DFTreeNode_cur->left);
        call_flag = false;
      } else {
        op_deque.pop_front();
        Function *func_target = CI->getCalledFunction();
        if (func_target == nullptr) { // encounter an indirect call
          // errs() << "indirect call during analyzing\n";
          auto iter = BB_array[index_cur].indirect_call_addr_map.find(CI);
          if (iter != BB_array[index_cur].indirect_call_addr_map.end()) {
            auto iter_2 = func_map.find(iter->second);
            if (iter_2 != func_map.end()) {
              func_target = CI->getModule()->getFunction(iter_2->second);
              if (!func_target->isDeclaration()) {
                op_left = findMatchedRet(func_target, index_cur);
                DFTreeNode_cur->left =
                    new DFTreeNode(saveOpInfo(op_left, index_cur));
                op_deque.push_front(DFTreeNode_cur->left);
                continue;
              } else {
                // errs() << "--- the indirect call calls a library function\n";
              }
            }
          }

        }
        // encounter a library call, end tracking
        if (func_target->isDeclaration()) { 
          //将memset的callsite存到bst中, 使之后作图更加直观
          if (func_target->getName() == "llvm.memset.p0i8.i64") {
            op_left = CI->getArgOperand(1);
            DFTreeNode_cur->left =
                new DFTreeNode(saveOpInfo(op_left, index_cur));
            op_deque.push_front(DFTreeNode_cur->left);
          }

          // see issue #15
          else if (func_target->getName() == "strcmp") {
            op_left = CI->getArgOperand(0);
            op_right = CI->getArgOperand(1);
            DFTreeNode_cur->left =
                new DFTreeNode(saveOpInfo(op_left, index_cur));
            op_deque.push_front(DFTreeNode_cur->left);
            DFTreeNode_cur->right =
                new DFTreeNode(saveOpInfo(op_right, index_cur));
            op_deque.push_front(DFTreeNode_cur->right);
          }

          else if (func_target->getName() == "strncmp") {
            op_left = CI->getArgOperand(0);
            op_right = CI->getArgOperand(1);
            DFTreeNode_cur->left =
                new DFTreeNode(saveOpInfo(op_left, index_cur));
            op_deque.push_front(DFTreeNode_cur->left);
            DFTreeNode_cur->right =
                new DFTreeNode(saveOpInfo(op_right, index_cur));
            op_deque.push_front(DFTreeNode_cur->right);
          }

          else if (func_target->getName() == "strrchr") {
            op_left = CI->getArgOperand(0);
            op_right = CI->getArgOperand(1);
            DFTreeNode_cur->left =
                new DFTreeNode(saveOpInfo(op_left, index_cur));
            op_deque.push_front(DFTreeNode_cur->left);
            DFTreeNode_cur->right =
                new DFTreeNode(saveOpInfo(op_right, index_cur));
            op_deque.push_front(DFTreeNode_cur->right);
          }

          else if (func_target->getName() == "memcmp") {
            // only consider first two argument of memcmp()
            op_left = CI->getArgOperand(0);
            op_right = CI->getArgOperand(1);
            DFTreeNode_cur->left =
                new DFTreeNode(saveOpInfo(op_left, index_cur));
            op_deque.push_front(DFTreeNode_cur->left);
            DFTreeNode_cur->right =
                new DFTreeNode(saveOpInfo(op_right, index_cur));
            op_deque.push_front(DFTreeNode_cur->right);
          }

          else if (func_target->getName() == "open") { 
            // only consider first argument of open()
            op_left = CI->getArgOperand(0);
            DFTreeNode_cur->left =
                new DFTreeNode(saveOpInfo(op_left, index_cur));
            op_deque.push_front(DFTreeNode_cur->left);
          }

          else if (func_target->getName() == "open64") {
            // only consider first argument of open()
            op_left = CI->getArgOperand(0);
            DFTreeNode_cur->left =
                new DFTreeNode(saveOpInfo(op_left, index_cur));
            op_deque.push_front(DFTreeNode_cur->left);
          }

          else if (func_target->getName() == "stat64") {
            op_left = CI->getArgOperand(0);
            DFTreeNode_cur->left =
                new DFTreeNode(saveOpInfo(op_left, index_cur));
            op_deque.push_front(DFTreeNode_cur->left);
          }

          else if (func_target->getName() == "unlink") {
            op_left = CI->getArgOperand(0);
            DFTreeNode_cur->left =
                new DFTreeNode(saveOpInfo(op_left, index_cur));
            op_deque.push_front(DFTreeNode_cur->left);
          }

          else if (func_target->getName() == "__isoc99_sscanf") {
            // only consider first two argument of sscanf()
            op_left = CI->getArgOperand(0);
            op_right = CI->getArgOperand(1);
            DFTreeNode_cur->left =
                new DFTreeNode(saveOpInfo(op_left, index_cur));
            op_deque.push_front(DFTreeNode_cur->left);
            DFTreeNode_cur->right =
                new DFTreeNode(saveOpInfo(op_right, index_cur));
            op_deque.push_front(DFTreeNode_cur->right);
          }

          else if (func_target->getName() == "strndup") {
            // consider all two arguments of strndup()
            op_left = CI->getArgOperand(0);
            op_right = CI->getArgOperand(1);
            DFTreeNode_cur->left =
                new DFTreeNode(saveOpInfo(op_left, index_cur));
            op_deque.push_front(DFTreeNode_cur->left);
            DFTreeNode_cur->right =
                new DFTreeNode(saveOpInfo(op_right, index_cur));
            op_deque.push_front(DFTreeNode_cur->right);
          }


        }
        // encounter a normal function call
        else if (!func_target->isDeclaration()) {

          if (func_target->getName() == "sqlite3_mprintf") {
            int op_num = CI->getNumArgOperands();
            if (op_num == 2) {
              op_left = CI->getArgOperand(1);
              DFTreeNode_cur->left =
                  new DFTreeNode(saveOpInfo(op_left, index_cur));
              op_deque.push_front(DFTreeNode_cur->left);
            } else if (op_num > 2) {
              op_left = CI->getArgOperand(1);
              op_right = CI->getArgOperand(2);
              DFTreeNode_cur->left =
                  new DFTreeNode(saveOpInfo(op_left, index_cur));
              op_deque.push_front(DFTreeNode_cur->left);
              DFTreeNode_cur->right =
                  new DFTreeNode(saveOpInfo(op_right, index_cur));
              op_deque.push_front(DFTreeNode_cur->right);
            }
            continue;
          } 

          else if (func_target->getName() == "lockState") {
            op_left = CI->getArgOperand(0);
            op_right = CI->getArgOperand(1);
            DFTreeNode_cur->left =
                new DFTreeNode(saveOpInfo(op_left, index_cur));
            op_deque.push_front(DFTreeNode_cur->left);
            DFTreeNode_cur->right =
                new DFTreeNode(saveOpInfo(op_right, index_cur));
            op_deque.push_front(DFTreeNode_cur->right);
            continue;
          } 
          
          else if (func_target->getName() == "does_file_exist") {
            op_left = CI->getArgOperand(0);
            DFTreeNode_cur->left =
                new DFTreeNode(saveOpInfo(op_left, index_cur));
            op_deque.push_front(DFTreeNode_cur->left);
            continue;
          }

          op_left = findMatchedRet(func_target, index_cur);
          DFTreeNode_cur->left = new DFTreeNode(saveOpInfo(op_left, index_cur));
          op_deque.push_front(DFTreeNode_cur->left);
        }
      }
      continue;
    }

    else if (InvokeInst *II = dyn_cast<InvokeInst>(inst_cur)) {
      if (call_flag) {
        op_deque.pop_front();
        op_left = II->getArgOperand(op_arg->getArgNo());
        DFTreeNode_cur->left = new DFTreeNode(saveOpInfo(op_left, index_cur));
        op_deque.push_front(DFTreeNode_cur->left);
        call_flag = false;
      } else {
        op_deque.pop_front();
        Function *func_target = II->getCalledFunction();
        // errs() << func_target->getName() << "\n";
        if (func_target == nullptr) {
          //暂时不做处理
        } else if (!func_target->isDeclaration()) {
          op_left = findMatchedRet(func_target, index_cur);
          // errs() << *op_left << "\n";
          DFTreeNode_cur->left = new DFTreeNode(saveOpInfo(op_left, index_cur));
          op_deque.push_front(DFTreeNode_cur->left);
        }
      }
      continue;
    }

    else if (BitCastInst *BCI = dyn_cast<BitCastInst>(inst_cur)) {
      op_deque.pop_front();
      op_left = BCI->getOperand(0);
      DFTreeNode_cur->left = new DFTreeNode(saveOpInfo(op_left, index_cur));
      op_deque.push_front(DFTreeNode_cur->left);
      continue;
    }

    else if (ReturnInst *RI = dyn_cast<ReturnInst>(inst_cur)) {
      op_deque.pop_front();
      op_left = RI->getReturnValue();
      DFTreeNode_cur->left = new DFTreeNode(saveOpInfo(op_left, index_cur));
      op_deque.push_front(DFTreeNode_cur->left);
      continue;
    }

    op_deque.pop_front();
    errs() << *inst_cur << "\n";
    errs() << "can not find\n";
  }

  errs() << "---------------traverseDFT--------------\n";
  traverseDFT(root, op_vec);
  drawDFT(root);
}

void DFA_manager(u32 index) {
  BasicBlock *BB_start = BB_array[index].BB_ptr;
  string draw_cmd;
  for (auto &I : *BB_start) {
    
    if (isa<InvokeInst>(&I) ||
        isa<CallInst>(&I)) {

      CallInst   * CI = dyn_cast<CallInst>(&I);
      InvokeInst * II = dyn_cast<InvokeInst>(&I);

      Function * calledFunc   = nullptr;
      Value    * calledValue  = nullptr;
      Value    * cond         = nullptr;
      unsigned int numArgOperands = 0;

      if (CI) {
        calledFunc = CI->getCalledFunction();
        calledValue = CI->getCalledValue();
        numArgOperands = CI->getNumArgOperands();
      } else {
        calledFunc = II->getCalledFunction();
        calledValue = II->getCalledValue();
        numArgOperands = II->getNumArgOperands();
      }

      vector<int> available_arguments;

      if (calledFunc != nullptr && 
          !calledFunc->getName().empty()) {
        available_arguments = libcall_arg[calledFunc->getName()];
        // errs() << "Function: " << calledFunc->getName() << "\n";
      } else {
        available_arguments = libcall_arg[callsite_map[&I]];
        // errs() << "Function: " << callsite_map[&I] << "\n";
      }

      // errs() << "available arguments: " << "\n";
      // for (int idx: available_arguments)
      //   errs() << idx << ' ';

      if ((calledFunc != nullptr &&
          find(libcall_vec.begin(), libcall_vec.end(), 
               calledFunc->getName()) != libcall_vec.end()) 
          ||
          (find(libcall_vec.begin(), libcall_vec.end(), 
                callsite_map[&I]) != libcall_vec.end())) {
        
        if (numArgOperands == 0) {
          errs() << "Warning: current syscall don't have arguments, so we stopped.\n";
        }

        for (s32 i = 0; i < numArgOperands; i++) {

          if (find(available_arguments.begin(), available_arguments.end(), i) == available_arguments.end()) {
            errs() << "Not in available arguments: " << i << "\n";
            continue;
          }

          if (CI) cond = CI->getArgOperand(i);
          else    cond = II->getArgOperand(i);
          errs() << "COND " << *cond << "\n";

          dataflowAnalysis(index, cond);
          draw_cmd = "dot -Tpng " + dot_path + " -o " + graph_folder_path +
                      cond_br_id + "-" + syscall_name + "-" + to_string(i) +
                      ".png";
          errs() << draw_cmd << "\n";
          system(draw_cmd.c_str());
        }

      }
    }
  }
}

void Rator::traverseFunc(Function *F) {
  if (exit_flag) {
    errs() << "Unreachable Inst Reached!\n";
    exit(-1);
  }
  BasicBlock *next_BB = &F->getEntryBlock();
  while (next_BB != nullptr) {
    next_BB = traverseBB(next_BB);
  }
  if (F == setjmp_F && longjmp_ret == true) { //已经退回到call setjmp_F
    longjmp_ret = false;
    setjmp_next = true; // 找到setjmp_I的位置继续运行
    next_BB = setjmp_BB;
    while (next_BB != nullptr) {
      next_BB = traverseBB(next_BB);
    }
  }
}

BasicBlock *Rator::traverseBB(BasicBlock *BB) {
  // BB_array_index keeps increasing, using cur_BB_array_index to record the
  // index of current BB
  u64 cur_BB_array_index = BB_array_index;
  recordBB(BB);
  for (auto &I : *BB) {
    if (end_traverse) {
      return nullptr;
    }

    if (setjmp_next && (setjmp_I != &I)) {
      continue;
    } else if (setjmp_next && (setjmp_I == &I)) {
      setjmp_next = false;
      continue;
    }

    if (longjmp_ret) {
      return nullptr;
    }

    if (StoreInst *StI = dyn_cast<StoreInst>(&I)) {
      //是否需要记录store的另一个operand 用作further analysis
      u64 store_ptr;
      u64 w_id;
      store_ptr = read_u64_from_file(rw_log);
      assert(store_ptr != 0xAAAAAAAAAAAAAAAA);

      w_id = read_u64_from_file(rw_log);


#ifdef RW_DEBUG
      u64 rw_id = rw_map[StI];
      if (rw_id == w_id) {
#if RW_DEBUG == 2
        errs() << "RW_ID Match " << rw_id << " " << w_id << "\n";
        errs() << "Inst: " << *StI << "\n";
#endif
        last_store = StI;
      } else {

        errs() << "RW_ID Not Match " << rw_id << " " << w_id << "\n";
        errs() << "Store/Load Inst in Record: " << "\n" 
               << rw_map_rev[w_id]->getParent()->getParent()->getName() << "\n"
               << *rw_map_rev[w_id] << "\n";

        errs() << "Store/Load Inst in Replay: " << "\n" 
               << StI->getParent()->getParent()->getName() << "\n"
               << *StI  << "\n";

        errs() << "\n" 
               << "Last BranchInst: " << *last_br     << "\n"
               << "Last Load      : " << *last_load   << "\n"
               << "Last Store     : " << *last_store  << "\n";

        exit(-1);
      }
#endif
      store_load_count++;
      BB_array[cur_BB_array_index].rw_vector.push_back(store_ptr);
    }

    else if (LoadInst *LI = dyn_cast<LoadInst>(&I)) {
      u64 load_ptr;
      u64 r_id;
      load_ptr = read_u64_from_file(rw_log);
      assert(load_ptr != 0xAAAAAAAAAAAAAAAA);

      r_id = read_u64_from_file(rw_log);

#ifdef RW_DEBUG
      u64 rw_id = rw_map[LI];
      if (rw_id == r_id) {
#if RW_DEBUG == 2
        errs() << "RW_ID Match " << rw_id << " " << r_id << "\n";
        errs() << "Inst: " << *LI << "\n";
#endif
        last_load = LI;
      } else {
        errs() << "RW_ID Not Match " << rw_id << " " << r_id << "\n";
        errs() << "Store/Load Inst in Record: " << "\n"
               << rw_map_rev[r_id]->getParent()->getParent()->getName() << "\n"
               << *rw_map_rev[r_id] << "\n";
        errs() << "Store/Load Inst in Replay: " << "\n"
               << LI->getParent()->getParent()->getName() << "\n"
               << *LI  << "\n";

        errs() << "\n" 
               << "Last BranchInst: " << *last_br     << "\n"
               << "Last Load      : " << *last_load   << "\n"
               << "Last Store     : " << *last_store  << "\n"
               << "Last Call      : " << *last_call << "\n"
               << "Last Call Func : " << last_call->getCalledFunction()->getName() << "\n"
               << "is Func Declare: " << last_call->getCalledFunction()->isDeclaration() << "\n";

        exit(-1);
      }
#endif
      store_load_count++;
      BB_array[cur_BB_array_index].rw_vector.push_back(load_ptr);
    }

    else if (BranchInst *BI = dyn_cast<BranchInst>(&I)) {
      if (BI->isConditional()) {
        u64 br_id = read_u64_from_file(br_log);
        assert(br_id != 0xAAAAAAAAAAAAAAAA);

        br_id_count++;
#ifdef BR_DEBUG
        if (br_id == br_map[BI]) {
#if BR_DEBUG == 2
          errs() << "BR_ID Match " << br_map[BI] << " " << br_id << "\n";
          errs() << "Inst: " << *BI << "\n";
#endif
          last_br = BI;
        } else {
          errs() << "BR_ID Not Match " << br_map[BI] << " " << br_id << " "
                 << br_id_count << "\n"
                 << "BranchInst in Record: " << br_map_rev[br_id]->getParent()->getParent()->getName() << "\n"
                                             << *br_map_rev[br_id] << "\n"
                 << "BranchInst in Replay: " << BI->getParent()->getParent()->getName() << "\n" 
                                             << *BI << "\n"
                 << "Last Inst: " << *last_br << "\n";
          exit(-1);
        }
#endif


#if ENABLE_VALIDATE
        u8 temp = getValByte(val_log_cache);
        if (temp == 0) {
          record_count++;
        } else {
          errs() << "0:Conditional Branch Validation Failed:" << int(temp)
                 << ":" << ++record_count << "\n";
          exit(-1);
        }
#endif

        // bool br_value = getBrCond(trace_log_cache);
        uint8_t br_value = getBrCond();
        br_value = br_value & 0x01;

#if BR_DEBUG == 2
        errs() << "Branch Counter: " << br_id_count << " "
                << "ID: " << br_id << " "
                << "Value: " << int(br_value) << "\n";
#endif
        if (br_value) {
          return BI->getSuccessor(0);
        } else {
          return BI->getSuccessor(1);
        }
      } else {
        return BI->getSuccessor(0);
      }
    }

    else if (SwitchInst *SI = dyn_cast<SwitchInst>(&I)) {

#if ENABLE_VALIDATE
      u8 temp = getValByte(val_log_cache);
      if (temp == 1) {
        ++record_count;
        // errs() << "1:Switch Validation Passed: " << temp << ":" <<
        // record_count << "\n";
      } else {
        errs() << "Switch Validation Failed:" << ++record_count << "\n";
        exit(-1);
      }
#endif

      u64 switch_id = read_u64_from_file(br_log);
      assert(switch_id >> 62 == 0x01UL);

      IRBuilder<> IRB(SI);
      // u32 switch_cond = getSwitchCond(trace_log_cache);
      u32 switch_cond = getSwitchCond();
      // errs() << I << "\n";
      for (auto Case : SI->cases()) {
        u32 case_cond = (u32)(Case.getCaseValue()->getZExtValue());
        if (case_cond == switch_cond) {
          return Case.getCaseSuccessor();
        }
      }
      return SI->getDefaultDest();
    }

    else if (isa<InvokeInst>(&I) ) {
      
      InvokeInst *II = dyn_cast<InvokeInst>(&I);

      u64 indirect_call_addr = 0;
      Function *targetFunc = nullptr;
      Value * calledValue = nullptr;

      targetFunc = II->getCalledFunction();
      calledValue = II->getCalledValue();

      if (targetFunc == nullptr) {

        u64 icall_id = read_u64_from_file(br_log);
        if (icall_id >> 62 != 0x2UL) {
          errs () << icall_id << "\n";
          exit(1);
        }
        indirect_call_addr = getIndirectCallAddr();

        if (Function *voidFunc = dyn_cast<Function>(calledValue->stripPointerCasts())) {
          targetFunc = voidFunc;

#if ENABLE_VALIDATE
          u8 temp = getValByte(val_log_cache);
          if (getValByte(val_log_cache) == 2) {
            record_count++;
          } else {
            errs() << "2:Invoke Validation Failed:" 
                  << int(temp) << ":" << ++record_count << "\n";
            exit(-1);
          }
#endif

        }

        else if (isa<GlobalAlias>(calledValue)) {

#if ENABLE_VALIDATE
          u8 temp = getValByte(val_log_cache);
          if (temp == 2) {
            record_count++;
          } else {
            errs() << "2:Invoke Validation Failed:" 
                   << int(temp) << ":" << ++record_count << "\n";
            exit(-1);
          }
#endif
          targetFunc = dyn_cast<Function>(dyn_cast<GlobalAlias>(calledValue)->getAliasee());
        }
      }

      if (targetFunc == nullptr) { // encounter an indirect invoke

#if ENABLE_VALIDATE
        u8 temp = getValByte(val_log_cache);
        if (temp == 2) {
          record_count++;
          // errs() << "2:Invoke Validation Passed: " << temp << ":" <<
          // record_count << "\n";
        } else {
          errs() << "2:Invoke Validation Failed:" << int(temp) << ":"
                << ++record_count << "\n";
          exit(-1);
        }
#endif

        string func_name;
        auto iter = func_map.find(indirect_call_addr);
        if (iter != func_map.end()) {
          func_name = iter->second;
          BB_array[cur_BB_array_index].indirect_call_addr_map[II] =
              indirect_call_addr;
          Function *indirect_call_func =
              II->getModule()->getFunction(func_name);
          if (indirect_call_func && !indirect_call_func->isDeclaration()) {
            traverseFunc(indirect_call_func);
            return II->getNormalDest();
            // continue;
          } else {
            return II->getNormalDest();
          }
        } else {
          // sometimes an indirect call will call a library call, we will just
          // skip it. temporarily, we just ignore all mismatches
          errs() << "no match function!"
                << "\n";
          return II->getNormalDest();
        }
      }

      if (targetFunc->getName() == "llvm.memcpy.p0i8.p0i8.i64") {
        u64 memcpy_ptr;
        memcpy_ptr = read_u64_from_file(rw_log);
        store_load_count++;
        BB_array[cur_BB_array_index].rw_vector.push_back(memcpy_ptr);

        memcpy_ptr = read_u64_from_file(rw_log);
        store_load_count++;
        BB_array[cur_BB_array_index].rw_vector.push_back(memcpy_ptr);

        memcpy_ptr = read_u64_from_file(rw_log);
        store_load_count++;
        BB_array[cur_BB_array_index].rw_vector.push_back(memcpy_ptr);
      }

      else if (targetFunc->getName() == "llvm.memset.p0i8.i64") {
        u64 memset_ptr;
        memset_ptr = read_u64_from_file(rw_log);
        store_load_count++;
        BB_array[cur_BB_array_index].rw_vector.push_back(memset_ptr);
        store_load_count++;
        memset_ptr = read_u64_from_file(rw_log);
        BB_array[cur_BB_array_index].rw_vector.push_back(memset_ptr);
      }

      else if (find(callbackNameList.begin(), callbackNameList.end(),
                    targetFunc->getName()) != callbackNameList.end()) {

        u64 fake_id = read_u64_from_file(br_log);
        assert(fake_id == 0xAAAAAAAAAAAAAAAA);
        // errs() << "consuming fake branch info: " << fake_id << "\n";
        fake_id = read_u64_from_file(br_log);
        // errs() << "consuming fake branch info: " << fake_id << "\n";
        // consume all control-flow log within callback functions
        while (fake_id != 0xBBBBBBBBBBBBBBBB) {
          
          switch((fake_id >> 62) & 0xff) {
            case 0x00: getBrCond();           break;
            case 0x01: getSwitchCond();       break;
            case 0x02: getIndirectCallAddr(); break;
            default: 
              errs() << "unexpected fake_id: " << fake_id << "\n";
              exit(1);
          }

#if ENABLE_VALIDATE
          getValByte(val_log_cache);
#endif

          fake_id = read_u64_from_file(br_log);
          // errs() << "consuming fake branch info: " << fake_id << "\n";
        }

        // consume all read/write log within callback functions
        u64 rw_ptr = read_u64_from_file(rw_log);
        assert(rw_ptr == 0xAAAAAAAAAAAAAAAA);
        // errs() << "consuming fake rw info: " << rw_ptr << "\n";
        while (rw_ptr != 0xBBBBBBBBBBBBBBBB) { 
          rw_ptr = read_u64_from_file(rw_log);
          // errs() << "consuming fake rw info: " << rw_ptr << "\n";
        }
      }

      if (!targetFunc->isDeclaration()) {
        traverseFunc(targetFunc);
        return II->getNormalDest();
      } else {
        if (targetFunc->getName() == "_setjmp" ||
            targetFunc->getName() == "__sigsetjmp") {
          errs() << "Catch Set Jump " << targetFunc->getName() << "\n";
          errs() << "SetJump: " << *II << "\n";

          setjmp_I = &I;
          setjmp_BB = I.getParent();
          setjmp_F = setjmp_BB->getParent();
          return II->getNormalDest();
        } else if (targetFunc->getName() == "longjmp" ||
                   targetFunc->getName() == "siglongjmp") {
          // traverseFunc会判断longjmp_ret，如果true，则一直ret到setjmp_F
          errs() << "Catch Long Jump " << targetFunc->getName() << "\n";
          errs() << "LongJump: " << *II << "\n";
          longjmp_ret = true;
          return nullptr;
        } else if (targetFunc->doesNotReturn()) {
          errs() << "No Return Function Called\n";
          errs() << *II << "\n";
          end_traverse = true;
          return nullptr;
        } else {
          return II->getNormalDest();
        }
      }

    }
    else if (isa<CallInst>(&I)) {
      CallInst * CI = dyn_cast<CallInst>(&I);

      u64 indirect_call_addr = 0;
      Function *targetFunc = nullptr;
      Value * calledValue = nullptr;
      
      targetFunc = CI->getCalledFunction();
      calledValue = CI->getCalledValue();

      if (targetFunc == nullptr) {

        u64 icall_id = read_u64_from_file(br_log);
        if (icall_id >> 62 != 0x2UL) {
          errs () << icall_id << "\n";
          exit(1);
        }
        indirect_call_addr = getIndirectCallAddr();

        if (Function *voidFunc = dyn_cast<Function>(calledValue->stripPointerCasts())) {
          targetFunc = voidFunc;

#if ENABLE_VALIDATE
          u8 temp = getValByte(val_log_cache);
          if (temp == 2) {
            record_count++;
          } else {
            errs() << "2:Call Validation Failed:" 
                   << int(temp) << ":" << ++record_count << "\n";
            exit(-1);
          }
#endif

        }

        else if (isa<GlobalAlias>(calledValue)) {
          targetFunc = dyn_cast<Function>(dyn_cast<GlobalAlias>(calledValue)->getAliasee());

#if ENABLE_VALIDATE
          u8 val_byte = getValByte(val_log_cache);
          if (val_byte == 2) {
            record_count++;
          } else {
            errs() << "2:Call Validation Failed:" 
                   << int(val_byte) << ":" << ++record_count << "\n";
            exit(-1);
          }
#endif

        }      
      }

      if (targetFunc && 
          find(libcall_vec.begin(), libcall_vec.end(),
               targetFunc->getName()) != libcall_vec.end()) {
        start_index = cur_BB_array_index;
        errs() << "--------Target Syscall Callsite Found----------\n";
        errs() << *CI << "\n";
        errs() << "start_index: " << start_index << "\n";
        end_traverse = true;
        return nullptr;
      }

      last_call = CI;

      // if (BB == target_BB) {
      //     start_index = cur_BB_array_index;
      //     errs() << "start_index: " << start_index << "\n";
      // }

      if (targetFunc == nullptr) { // encounter an indirect call

#if ENABLE_VALIDATE
        u8 temp = getValByte(val_log_cache);
        if (temp == 2) {
#ifdef BR_DEBUG
          //   errs() << "Indirect Call Validation Passed\n";
          //   errs() << "---------------------------------------------\n";
          //   errs() << *CI << "\n";
          //   errs() << "---------------------------------------------\n";
#endif
          ++record_count;
        } else {
          errs() << "Indirect Call Validation Failed:" 
                 << temp << ":" << ++record_count << "\n";
#if BR_DEBUG == 2
          errs() << "---------------------------------------------\n";
          errs() << *CI << "\n";
          errs() << "---------------------------------------------\n";
          errs() << *BB << "\n";
#endif
          exit(-1);
        }
#endif

        string func_name;
        auto iter = func_map.find(indirect_call_addr);
        if (iter != func_map.end()) {
          func_name = iter->second;
          BB_array[cur_BB_array_index].indirect_call_addr_map[CI] =
              indirect_call_addr;
          callsite_map[CI] = func_name;

          if (find(libcall_vec.begin(), libcall_vec.end(), func_name) !=
              libcall_vec.end()) {
            start_index = cur_BB_array_index;
            errs() << "--------Target Syscall Callsite Found----------\n";
            errs() << *CI << "\n";
            errs() << "start_index: " << start_index << "\n";
            end_traverse = true;
            return nullptr;
          }

          // errs() << "Entering function " << func_name << "\n";
          Function *indirect_call_func =
              CI->getModule()->getFunction(func_name);
          if (indirect_call_func && !indirect_call_func->isDeclaration()) {
            // errs() << "Indirect Call-------" << "\n";
            traverseFunc(indirect_call_func);
            continue;
          } else {
            // errs() << "Call a library call via indirect call" << func_name <<"\n";
            continue;
          }
        } else {

          errs() << *CI << "\n";
          errs() << "Call not match indirect addr in func_map: "
                <<  indirect_call_addr  
                 << "\n";
          continue;
        }
      }

      if (targetFunc->getName() == "llvm.memcpy.p0i8.p0i8.i64") {
        u64 memcpy_ptr;
        memcpy_ptr = read_u64_from_file(rw_log);
        store_load_count++;
        BB_array[cur_BB_array_index].rw_vector.push_back(memcpy_ptr);

        memcpy_ptr = read_u64_from_file(rw_log);
        store_load_count++;
        BB_array[cur_BB_array_index].rw_vector.push_back(memcpy_ptr);

        memcpy_ptr = read_u64_from_file(rw_log);
        store_load_count++;
        BB_array[cur_BB_array_index].rw_vector.push_back(memcpy_ptr);
      }

      else if (targetFunc->getName() == "llvm.memset.p0i8.i64") {
        u64 memset_ptr;
        memset_ptr = read_u64_from_file(rw_log);
        store_load_count++;
        BB_array[cur_BB_array_index].rw_vector.push_back(memset_ptr);

        store_load_count++;
        memset_ptr = read_u64_from_file(rw_log);
        BB_array[cur_BB_array_index].rw_vector.push_back(memset_ptr);
      }

      else if (find(callbackNameList.begin(), callbackNameList.end(),
                    targetFunc->getName()) != callbackNameList.end()) {

        u64 fake_id = read_u64_from_file(br_log);
        assert(fake_id == 0xAAAAAAAAAAAAAAAA);
        // errs() << "consuming fake branch info: " << fake_id << "\n";
        fake_id = read_u64_from_file(br_log);
        // errs() << "consuming fake branch info: " << fake_id << "\n";
        // consume all control-flow log within callback functions
        while (fake_id != 0xBBBBBBBBBBBBBBBB) {
          
          switch((fake_id >> 62) & 0xff) {
            case 0x00: getBrCond();           break;
            case 0x01: getSwitchCond();       break;
            case 0x02: getIndirectCallAddr(); break;
            default: 
              errs() << "unexpected fake_id: " << fake_id << "\n";
              exit(1);
          }

#if ENABLE_VALIDATE
          getValByte(val_log_cache);
#endif

          fake_id = read_u64_from_file(br_log);
          // errs() << "consuming fake branch info: " << fake_id << "\n";
        }

        // consume all read/write log within callback functions
        u64 rw_ptr = read_u64_from_file(rw_log);
        assert(rw_ptr == 0xAAAAAAAAAAAAAAAA);
        // errs() << "consuming fake rw info: " << rw_ptr << "\n";
        while (rw_ptr != 0xBBBBBBBBBBBBBBBB) { 
          rw_ptr = read_u64_from_file(rw_log);
          // errs() << "consuming fake rw info: " << rw_ptr << "\n";
        }
      }

      /* Filter intrinsic function out */
      // if (targetFunc->isIntrinsic()) {
      //     continue;
      // }
      if (!targetFunc->isDeclaration()) {
        traverseFunc(targetFunc);
        continue;
      } else {
        if (targetFunc->getName() == "_setjmp"||
            targetFunc->getName() == "__sigsetjmp") {
          errs() << "Catch Set Jump " << targetFunc->getName() << "\n";
          errs() << "SetJump: " << *CI << "\n";
          setjmp_I = CI;
          setjmp_BB = CI->getParent();
          setjmp_F = setjmp_BB->getParent();
          continue;
        } else if (targetFunc->getName() == "longjmp"||
                   targetFunc->getName() == "siglongjmp") {
          // traverseFunc会判断longjmp_ret，如果true，则一直ret到setjmp_F
          errs() << "Catch Long Jump " << targetFunc->getName() << "\n";
          errs() << "LongJump: " << *CI << "\n";
          longjmp_ret = true;
          return nullptr;
        } else if (targetFunc->doesNotReturn()) {
          errs() << "No Return Function Called\n";
          errs() << *CI << "\n";
          end_traverse = true;
          return nullptr;
        } else {
          // errs() << "CallInst.isDeclaration() && !targetFunc->doesNotReturn()\n";
        }
      }
    }

    else if (isa<ReturnInst>(I)) {
      if (I.getFunction()->getName() == "main") {
        errs()
            << "--------------------\nTraverse End\n----------------------\n";
      }
      return nullptr;
    }

    else if (isa<UnreachableInst>(I)) {
#ifdef BR_DEBUG
      errs() << "EXIT_FLAG = TRUE\n";
      errs() << I << "\n";
#endif
      exit_flag = true;
      return nullptr;
    }
  }

  llvm_unreachable("seems a bad Basic Block");
}

static void initFiles() {

  trace_log = fopen(TRACE_LOG_FILE, "rb");
  if (trace_log == NULL) {
    fprintf(stderr, "cannot open trace log file: %s\n", TRACE_LOG_FILE);
    exit(-1);
  }

  trace_log_cache = (u8 *)malloc(LOG_CACHE_SIZE);
  if (trace_log_cache == NULL) {
    fprintf(stderr, "failed to allocate trace log cache\n");
    exit(-1);
  }

  val_log = fopen(VAL_LOG_FILE, "rb");
  if (val_log == NULL) {
    fprintf(stderr, "cannot open value log file: %s\n", VAL_LOG_FILE);
    exit(-1);
  }

  val_log_cache = (u8 *)malloc(LOG_CACHE_SIZE);
  if (val_log_cache == NULL) {
    fprintf(stderr, "failed to allocate val log cache\n");
    exit(-1);
  }

  rw_log = fopen(RW_LOG_FILE, "rb");
  if (rw_log == NULL) {
    fprintf(stderr, "cannot open store/load log file: %s\n", RW_LOG_FILE);
    exit(-1);
  }

  br_log = fopen(BR_LOG_FILE, "rb");
  if (br_log == NULL) {
    fprintf(stderr, "cannot open br log file: %s\n", BR_LOG_FILE);
    exit(-1);
  }

  for (int i = 0; i < BB_ARRAY_SIZE; i++) {
    BB_array.push_back(BB_info());
  }

  if (BB_array.empty()) {
    fprintf(stderr, "failed to allocate bb array\n");
    exit(-1);
  }

  struct stat st;
  stat(TRACE_LOG_FILE, &st);
  file_size = st.st_size;

  stat(VAL_LOG_FILE, &st);
  val_file_size = st.st_size;
}

void rw_map_gen(Module &M) {
  u64 rw_id = 0;
  for (auto &F : M) {
    for (auto &BB : F) {
      for (auto &I : BB) {
        if (StoreInst *StI = dyn_cast<StoreInst>(&I)) {
          rw_map[StI] = rw_id;
          rw_map_rev[rw_id] = StI;
          rw_id++;
        } else if (LoadInst *LI = dyn_cast<LoadInst>(&I)) {
          rw_map[LI] = rw_id;
          rw_map_rev[rw_id] = LI;
          rw_id++;
        }
      }
    }
  }
}

void br_map_gen(Module &M) {
  u64 br_id = 0;
  for (auto &F : M) {
    for (auto &BB : F) {
      for (auto &I : BB) {
        if (BranchInst *BI = dyn_cast<BranchInst>(&I)) {
          if (BI->isConditional()) {
            br_map[BI] = br_id;
            br_map_rev[br_id] = BI;
            br_id++;
          }
        }
      }
    }
  }
}

bool Rator::runOnModule(Module &M) {
  /* Default setting for BB arrays */
  initFiles();
  func_map_gen();
  proc_map_gen();
  libcall_map_gen();
#ifdef RW_DEBUG
  rw_map_gen(M);
#endif
#ifdef BR_DEBUG
  br_map_gen(M);
#endif
  typedef multimap<string, string>::iterator multiMapItor;
  pair<multiMapItor, multiMapItor> pos = libcall_map.equal_range(syscall_name);
  while (pos.first != pos.second) {
    libcall_vec.push_back(pos.first->second);
    ++pos.first;
  }

  initFiles();
  // loadData(trace_log, trace_log_cache, file_size, load_time, byte_index);
  loadData(val_log, val_log_cache, val_file_size, val_load_time,
           val_byte_index);
  Function *main_func = M.getFunction("main");
  traverseFunc(main_func);
  if (start_index == 0) {
    errs() << "No Syscall Callsite Found\n";
  } else {
    printBB(start_index, num_BB_print);
    DFA_manager(start_index);
  }

  //Removes all elements in vector
  BB_array.clear();

  //Frees the memory which is not used by the vector
  BB_array.shrink_to_fit();

  return true;
}

int main(int argc, char **argv) {
  if (argc < 5) {
    errs() << "Usage: " << argv[0]
           << " <IR file> <syscall name> <num_BB_print> <plot_folder_path>\n";
    return 1;
  }
  SMDiagnostic Err;
  LLVMContext Context;
  std::unique_ptr<Module> Mod(parseIRFile(argv[1], Err, Context));
  if (!Mod) {
    Err.print(argv[0], errs());
    return 1;
  }
  cond_br_id = argv[2];
  syscall_name = argv[3];
  // arg_id = atoi(argv[3]);
  num_BB_print = atoi(argv[4]);
  dot_path = argv[5];
  graph_folder_path = dot_path.substr(0, dot_path.rfind("/") + 1);

  // Create a pass manager and fill it with the passes we want to run.
  legacy::PassManager PM;
  PM.add(new Rator());
  PM.run(*Mod);
  return 0;
}
