import os
import sys
import subprocess
import copy

syscall_name_list = []
fuzzing_report = "log/flip_result"
libcall_file = "log/libcall"
queue_path = "./output/queue/"
queue_backup = "./output/queue.bak/"

# for generating lib_func_map
proc_map = "./log/proc_map"
lib_func_map = "./log/lib_func_map"
readelf_tmp = "./log/readelf_tmp"

if len(sys.argv) < 6:
    print("Usage: python {} <bitcode> <dot_file> <branch_arg> -- <record_binary> [arg1, arg2, @@]".format(sys.argv[0]))
    sys.exit(0)

bc_path = sys.argv[1]
dot_path = sys.argv[2]
branch_arg_mode = sys.argv[3]
# argv[4] is '--', skip. 
program_path = sys.argv[5]
program_command = sys.argv[5:]

def restore_corpus():
    if not os.path.exists(queue_backup):
        os.system("cp -r {} {}".format(queue_path, queue_backup))
        # print("[+] Create corpus backup!")
    else:
        os.system("rsync -aru --delete {} {}".format(queue_backup, queue_path))
        # print("[+] Restore corpus !")


def create_lib_func_map():
    lib_list = []
    sub_str = "/usr/lib/"

    f = open(lib_func_map, "w")
    for line in open(proc_map):
        if (sub_str in line):
            lib = sub_str + line.split(sub_str)[1].replace("\n", "")
            if lib in lib_list:
                continue

            base_addr = line.split("-")[0]
            readelf_cmd = "readelf -s " + lib + " | grep FUNC > " + readelf_tmp
            os.system(readelf_cmd)
            for line2 in open(readelf_tmp):
                if line2.split(":")[1].split(" ")[1] == "0000000000000000":
                    continue

                offset = line2.split(":")[1].split(" ")[1]
                func_name = line2.split("@")[0].split(" ")[-1].replace("\n", "")
                real_addr = str(int(base_addr, 16) + int(offset, 16))
                f.write(real_addr + " " + func_name + "\n")

            lib_list.append(lib)
    f.close()

def run_record_binary(testcase_id):
    default_timeout = "5s"
    record_cmd = "timeout {} ".format(default_timeout) 
    input_file = os.path.join(queue_path, testcase_id)

    cmdline = copy.deepcopy(program_command)

    is_stdin = True if "@@" not in cmdline else False
    if is_stdin:
        record_cmd += " ".join(cmdline) + " < " + input_file
    else:
        file_pattern_idx = cmdline.index("@@")
        cmdline[file_pattern_idx] = input_file
        record_cmd += " ".join(cmdline)
    
    # record_cmd += " 1> log/record_stdout"
    # record_cmd += " 2> log/record_stderr"

    print(record_cmd)
    subprocess.run(record_cmd, shell=True, env=os.environ)
    # os.system("python3 rm_gen_files.py")
    # create lib_func_map after executing record binary
    create_lib_func_map()

def create_func_map():
    if not os.path.exists("log/func_map"):
        objdump_cmd = "objdump -d " + program_path + " | grep \">:\" > log/func_map"
        os.system(objdump_cmd)

def create_grep_result():
    if not os.path.exists("log/grep_result"):
        collect_cmd = "grep -B 2 \"New Syscalls:-\" " + fuzzing_report + " > log/grep_result"
        os.system(collect_cmd)

def create_temp_dot():
    dot_dir = os.path.dirname(dot_path)

    if not os.path.exists(dot_dir):
        os.mkdir(dot_dir)
    
    if not os.path.exists(dot_path):
        # create temp.dot
        os.close(os.open(dot_path, os.O_CREAT))

def run_rator_br(branch_id):
    replay_cmd = "./rator " + bc_path + " " + branch_id + " 0 " + dot_path
    print(replay_cmd)
    subprocess.run(replay_cmd, shell=True, env=os.environ)

def run_rator_arg(branch_id, syscall_name_list):
    for syscall in syscall_name_list:
        replay_cmd = "./rator_arg " + bc_path + " " + branch_id + " " + syscall + " 0 " + dot_path 
        print(replay_cmd)
        try:
            subprocess.check_output(replay_cmd, shell=True, env=os.environ)
        except subprocess.CalledProcessError:
            print("Exception happened in rator_arg")

def collectRecord(branch_id, testcase_id, syscall_name_list):
    os.environ["FLIP_MODE"] = "1"
    os.environ["FLIP_BRANCH_ID"] = branch_id
    print("------------Analyzy Branch: " + branch_id + " ---------------")
    print("Syscalls:", syscall_name_list, "\n")

    restore_corpus()
    run_record_binary(testcase_id)

    if (branch_arg_mode == "br"):
        run_rator_br(branch_id)
    elif (branch_arg_mode == "arg"):
        run_rator_arg(branch_id, syscall_name_list)


def collectFuzzingResult():
    create_func_map()
    create_grep_result()
    create_temp_dot()

    if branch_arg_mode == "arg" and not os.path.exists(libcall_file):
        print("rator_arg requires `{}`.".format(libcall_file))
        print("please place it before runing script.")
        sys.exit(0)

    for line in open("log/grep_result"):
        if (line.startswith("Flip branch")):
            branch_id = line.split(" ")[2]
        elif(line.startswith("Testcase:")):
            testcase_id = line[9:].replace("\n", "")
        elif(line.startswith("New Syscalls:")):
            syscall_name_list = line.replace("\n", "").replace(" ", "").split("-")[1:]
            collectRecord(branch_id, testcase_id, syscall_name_list)


def main():
    collectFuzzingResult()
    


if __name__=="__main__":
    main()