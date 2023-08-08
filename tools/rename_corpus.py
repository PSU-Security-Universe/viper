import os
import sys

testcase_folder = sys.argv[1]

files = os.listdir(testcase_folder)

file_id = 1

for file in files:
    new_file_name = str(file_id)
    os.rename(testcase_folder + file, testcase_folder + new_file_name)
    file_id += 1
