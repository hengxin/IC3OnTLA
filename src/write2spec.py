# 导入os模块，用来检查文件是否存在
import os
import re
# 定义一个函数，用来往TLA+ specification文件中写入内容
def write_new_frame_to_spec(filename, content,n):
    # 检查文件是否存在，如果不存在，就创建一个新文件
    if not os.path.exists(filename):
        with open(filename, "w") as f:
            pass
    # 以追加模式打开文件
    with open(filename, "a") as f:
        # 写入内容到文件末尾
        text = f.read()
        match = re.search("F"+str(n)+" == (.*)", text)
        if match is not None:
            print("Frame existes!")
            return False
        else:
            f.write("F"+n+" == "+content)
            return True

def updateFrameInv(filename,n,content):
    #todo:需要优化
    with open(filename, "r+") as f:
        # 读取文件的所有内容
        text = f.read()
        # 使用正则表达式匹配Frame
        match = re.search("F"+str(n)+" == (.*)", text)
        print(match.group(1))
        f.seek(0)
        f.truncate()  # 清空文件
        f.write(text.replace(match.group(1), content))

def write_new_inv_to_spec(content):
    # 检查文件是否存在，如果不存在，就创建一个新文件
    filename = "/Users/fruitfighter/Desktop/IC3onTLA+/spec/two_phase_commit.tla"
    # 以追加模式打开文件
    with open(filename, "a") as f:
        # 写入内容到文件末尾
        f.write(content)

def del_the_last_one():
    with open("/Users/fruitfighter/Desktop/IC3onTLA+/spec/two_phase_commit.tla", "r+") as f:
        current_position = previous_position = f.tell()
        while f.readline():
            previous_position = current_position
            current_position = f.tell()
        f.truncate(previous_position)