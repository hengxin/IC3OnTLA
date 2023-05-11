from typing import List, Tuple


class StateFile:
    def __init__(self):
        #记录正例
        self.constraint_pos: List
        #记录反例
        self.constraint_neg: List
        #记录imp
        self.constraint_imp: List[Tuple]


#将一个apalache输出的文件中的状态写入到state状态集合文件中
def write_to_state_file(apalache_file_path,state_file_path) -> StateFile:
    #过程中应该需要更新StateFile
    return True