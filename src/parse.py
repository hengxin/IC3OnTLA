# 导入re模块，用来处理正则表达式
import json

# 定义一个函数，用来读取TLA+ specification文件里的各种信息
# 可以与用户输入做check
def parse_tla_information_with_json(spec):
    # Opening JSON file
    filepath = "spec2json/"+ spec+ "_output.json"
    f = open(filepath,"r")
    text = f.read()
    data = json.loads(text)
    # 一般只有一个module，如果出现其余的module 试图去迭代更新这个函数方法
    for index in data["modules"][0]["declarations"]:
        kind = index["kind"]
        if kind == "TlaConstDecl":
            # 对于constant来说，需要获取常量的具体信息
            return True
        elif kind == "TlaVarDecl":
            # 对于var来说，需要通过TypeOk来推测变量的具体信息
            return True
        elif kind == "TlaOperDecl":
            # 也可能是我们需要的信息 比如msg \in Message 就需要推测Message中的信息?
            return True
        elif kind == "TlaAssumeDecl":
            return True
        elif kind == "TlaTheoremDecl":
            return True
    f.close()
    return True
