# record origin files in root folders
import os 
import shutil

ori_fd = open('ori_files.txt','w+')
# in  root_folders
ori_files = os.listdir("./")
for file in ori_files:
    #print(file)
    ori_fd.write(file+'\n')
ori_fd.close()

os.system("cp -r corpus/ corpus_bak/")
