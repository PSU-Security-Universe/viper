import os 
import sys

proc_map = "./log/proc_map"
lib_func_map = "./log/lib_func_map"
readelf_tmp = "./log/readelf_tmp"
sub_str = "/usr/lib/"
lib_list = []

f = open(lib_func_map, "w")

for line in open(proc_map):
    if (sub_str in line):
        lib = sub_str + line.split(sub_str)[1].replace("\n", "")
        if lib in lib_list:
            continue
        else:
            base_addr = line.split("-")[0]
            readelf_cmd = "readelf -s " + lib + " | grep FUNC > " + readelf_tmp
            os.system(readelf_cmd)
            for line2 in open(readelf_tmp):
                if line2.split(":")[1].split(" ")[1] == "0000000000000000":
                    continue
                else:
                    offset = line2.split(":")[1].split(" ")[1]
                    func_name = line2.split("@")[0].split(" ")[-1].replace("\n", "")
                    real_addr = str(int(base_addr, 16) + int(offset, 16))
                    f.write(real_addr + " " + func_name + "\n")

            lib_list.append(lib)

f.close()

