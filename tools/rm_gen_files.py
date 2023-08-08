import os 
import shutil

path = os.path.dirname(os.path.abspath(__file__))+'/'

print(path)
while_list = ['output','dot','log', 'replayer', 'replayer_arg', 'corpus_bak','lib_func_map_gen.py','stdout.txt','stderr.txt']
corpus_list= []
# step one: append while_list

for line in open("./ori_files.txt"):  
    #print(line)
    while_list.append(line[:-1])

# step two: delete file & folders not in while_list

cur_files = os.listdir("./")
for file in cur_files:
    if file not in while_list:
        file_path = path + file
        #print("Ready to delete: " + file_path)
        try:
            os.remove(file_path)
        except IsADirectoryError:
            shutil.rmtree(file_path, ignore_errors=True)


# step three: recover corpus folder
if not os.path.exists('./corpus_bak'):
    print("Didn't find corpus_bak, please check whether rec_ori_files.py creates corpus_bak")
else:
    shutil.rmtree("./corpus")
    shutil.copytree("./corpus_bak", "./corpus")

#shutil.rmtree('./corpus', ignore_errors=True)
#os.system("mv corpus_bak corpus")


