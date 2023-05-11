#需要一个函数专门帮助我处理logic问题
from typing import List, Dict, Tuple,Set
import copy
class State(object):
    def __init__(self):
        self.constants: Dict[str, Set[str]] = {}
        self.sorts: Dict[str, Set[str]] = {}
        self.records: Dict[str, Dict[str, str]] = {}
        self.records_set: Dict[str, Set[str]] = {}
        self.tuples: Dict[str, Tuple[str]] = {}
        self.trans_constants: Dict[str,str] = {}
        self.isPositive = True
    def add_trans_constant(self, name: str, elem: str) -> bool:
        if name in self.constants:
            return False
        self.trans_constants[name] = elem
        return True
    def load(self,checker):
        self.constants=  copy.deepcopy(checker.constants)
        self.sorts =  copy.deepcopy(checker.sorts)
        self.records =  copy.deepcopy(checker.records)
        self.tuples = copy.deepcopy(checker.tuples)
    def update(self,isPos,num,spec):
        if isPos:
            state_name = "Positive_State"+str(num) + "=="
        else:
            state_name = "Negative_State"+str(num) + "=="
            self.isPositive = False
        filepath = "state/" + spec + "_states.tla"
        with open(filepath, "r") as f:
            lines = f.readlines()
            #预处理
            for i in range(0,len(lines)):
                lines[i] = lines[i].replace(" ", "")
                lines[i] = lines[i].strip()
            for i in range(0,len(lines)):
                if lines[i] == state_name:
                    j = i+1
                    while j < len(lines):
                        if lines[j] == "End":
                            return True
                        parse_str = lines[j]
                        while "/\\" not in lines[j+1] and lines[j+1]!="End":
                            j += 1
                            parse_str += lines[j]
                        parse_str = parse_str.strip("/\\")
                        info = parse_str.split("=")
                        isConstant = False
                        isSort = False
                        isRecord = False
                        for name in self.constants.keys():
                            if info[0] == name:
                                isConstant = True
                                info[1] = info[1].strip("{")
                                info[1] = info[1].strip("}")
                                info[1] = info[1].replace("\"","")
                                if info[1] == "":
                                    self.constants[info[0]] = []
                                else:
                                    elements = info[1].split(",")
                                    for index in self.constants[info[0]]:
                                        if index not in elements:
                                            self.constants[info[0]].remove(index)
                        if not isConstant:
                            for name in self.sorts.keys():
                                if info[0] == name:
                                    isSort = True
                                    info[1] = info[1].strip("{")
                                    info[1] = info[1].strip("}")
                                    info[1] = info[1].replace("\"", "")
                                    if info[1] == "":
                                        self.sorts[info[0]] = []
                                    else:
                                        sorts = copy.deepcopy(self.sorts[info[0]])
                                        elements = info[1].split(",")
                                        for index in sorts:
                                            if index not in elements:
                                                self.sorts[info[0]].remove(index)
                                    break
                        if not (isConstant & isSort):
                            for name in self.records.keys():
                                if info[0] == name:
                                    isRecord = True
                                    info[1] = info[1].strip("SetAsFun({<<")
                                    info[1] = info[1].strip(">>})")
                                    info[1] = info[1].replace("\"", "")
                                    if info[1] == "":
                                        self.records[info[0]] = {}
                                    else:
                                        elements = info[1].split(">>,<<")
                                        record = {}
                                        for element in elements:
                                            key_value = element.split(",")
                                            record[key_value[0]] = key_value[1]
                                        self.records[info[0]].update(record)
                        if not (isConstant | isSort | isRecord):
                            ##todo 后续做修改
                            print(1)
                        j+=1









