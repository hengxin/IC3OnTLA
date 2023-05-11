from typing import Dict, Tuple, Set


class TypeChecker(object):
    constants: Dict[str, Set[str]] = {}
    created_const: Dict[str,Set[str]] = {}
    sorts: Dict[str, Set[str]] = {}
    records: Dict[str, Dict[str, str]] = {}
    records_set: Dict[str, Set[str]] = {}
    tuples: Dict[str, Tuple[str]] = {}
    def typecheck(self):
        #spec = input("Please input your specification name.")
        #constants_name = input("Please enter your constants_info and separate it with spaces")
        constants_name = "NODE"
        for i in constants_name.split():
            self.constants[i] = []
            self.created_const[i] = []
            #constant_elements = input("Please enter the initialized variables and separate it with spaces")
            constant_elements = "n1_OF_NODE n2_OF_NODE n3_OF_NODE"
            for j in constant_elements.split():
                self.constants[i].append(j)
        print("constants type check is ok")

        #sorts_name = input("Please enter your sorts_info and separate it with spaces")
        sorts_name = "alive decide_abort decide_commit go_abort go_commit vote_no vote_yes"
        for i in sorts_name.split():
            self.sorts[i] = []
            #sort_element = input("Please enter the expected variables and separate it with spaces")
            sort_element = "n1_OF_NODE n2_OF_NODE n3_OF_NODE"
            for j in sort_element.split():
                self.sorts[i].append(j)
        print("sorts type check is ok")

        # records_name = input("Please enter your records_info and separate it with spaces")
        # for i in records_name.split():
        #     self.records[i] = {}
        #     self.records_set[i] = []
        #     record_element = input("Please enter the expected variables with comma and separate it with spaces")
        #     for j in record_element.split():
        #         key_value =  j.split(",")
        #         if len(key_value) != 2:
        #             print("Format error!")
        #             return False
        #         else:
        #             self.records[i][key_value[0]] = ""
        #             self.records_set[i].append(str(key_value[0])+","+str(key_value[1]))
        # print("records type check is ok")
        #
        # tuples_name = input("Please enter your tuples_info and separate it with spaces")
        # for i in tuples_name.split():
        #     tuple_element = input("Please enter the expected variables and separate it with spaces")
        #     elements =  tuple_element.split()
        #     self.tuples[i] = tuple(elements)
        # print("tuples type check is ok")

        return self
    #嵌套关系！