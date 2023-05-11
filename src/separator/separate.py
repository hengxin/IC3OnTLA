import z3

from typing import List,Tuple, Iterable, Dict,DefaultDict,Iterator,Set
from src.separator.logic import State
from src.typecheck import TypeChecker
from collections import defaultdict
import copy
from src.separator.matrix import infer_matrix

QuantifierStr = Tuple[bool, str]
InstId = Tuple[str, Tuple[str, ...]]

class VarSet(object):
    def __init__(self) -> None:
        self.vars: Set[int] = set()
        self.pos: Set[int] = set()
        self.neg: Set[int] = set()
    def add(self, v: int, polarity: bool) -> None:
        self.vars.add(v)
        if polarity:
            self.pos.add(v)
        else:
            self.neg.add(v)
    def __iter__(self) -> Iterator[int]: return iter(self.vars)

class CollapseCache(object):
    def __init__(self):
        self.states : List[State] = []
        self.typechecker : TypeChecker = None
        self.cache: Dict[InstId, int] = {}
        self.collapsed: Dict[str, int] = {}
        self.assignments: List[InstId] = []
        self.all_assignments: DefaultDict[int, List[InstId]] = defaultdict(list)
    def load(self,checker):
        self.typechecker = copy.deepcopy(checker)
    def add_state(self, state: State) -> None:
        self.states.append(state)
    def get(self, index: int, asgn: List[str]) -> int:
        assignment = tuple(asgn)
        # ensure elems are integers referring to elements of model index
        #assert all(e in self.states[index].constants for e in assignment)
        # fast path if assignment has been seen before
        if (index, assignment) in self.cache:
            return self.cache[(index, assignment)]
        # collapse model
        key = collapse(self.states[index], self.typechecker, assignment)
        print(key)
        if key not in self.collapsed:
            r = len(self.collapsed)
            self.collapsed[key] = r
            self.assignments.append((index, assignment))
        else:
            r = self.collapsed[key]
        self.all_assignments[r].append((index, assignment))
        self.cache[(index, assignment)] = r
        return r
    def get_concrete(self, i: int) -> State:
        (index, assignment) = self.assignments[i]
        M = copy.deepcopy(self.states[index])
        for var_i, element in enumerate(assignment):
            M.add_trans_constant("x_"+str(var_i), element)
        return M
    def get_example(self, i: int) -> Tuple[int, Tuple[int, ...]]:
        return self.assignments[i]
    def fo_type_count(self) -> int:
        return len(self.collapsed)
    def __len__(self) -> int:
        return len(self.assignments)

#将state压缩
def collapse(state:State,typechecker:TypeChecker,assignment: Iterable[str]) -> str:
    mapping: Dict[str, int] = {}  # store the correspondence between elements and identifiers
    const_type: List[str] = []
    const = [] # store the collapsed constants
    sorts = []  # store the sorts of identifiers
    records = []  # store the collapsed records
    tuples = []  # store the collapsed tuples

    def get_element(e: str) -> int:
        # check if e already has a corresponding identifier in mapping, if not, assign a new identifier to e and add its sort to sorts; then return its identifier
        if e not in mapping:
            mapping[e] = len(mapping)
            for key in state.constants.keys():
                if e in state.constants[key]:
                    const_type.append(key)
                    break
        return mapping[e]

    for key in sorted(state.trans_constants.keys()):
        const.append(get_element(state.trans_constants[key]))

    for e in assignment:
        const.append(get_element(e))

    for sort in sorted(state.sorts.keys()):
        collapsed_sorts = []
        for element in state.sorts[sort]:
            if element in mapping.keys():
                collapsed_sorts.append(tuple([mapping[element]]))
        collapsed_sorts.sort()
        sorts.append(collapsed_sorts)

    for record in sorted(state.records.keys()):
        elements = state.records[record]
        collapsed_elements = []
        str_elements = []
        key_elements = []
        all_record =  typechecker.records_set[record]
        for key in elements:
            element_str = str(key) + "," + str(elements[key])
            str_elements.append(element_str)
            key_elements.append(key)
        for i in all_record:
            for j in range(0,len(str_elements)):
                if i == str_elements[j]:
                    collapsed_elements.append(key_elements[j])
            else:
                collapsed_elements.append('')
        records.append(collapsed_elements)
    #todo:之后支持tuples
    return repr((const_type, sorts, records,const))  # return a string that represents the collapsed model

def formula_for_state(state_index: int, assignment: List[str], prefix_i: int, prefix: List[QuantifierStr], collapsed: CollapseCache,vars:VarSet,ignore_label:bool = False) -> z3.ExprRef:
    #获得state
    state = collapsed.states[state_index]
    if prefix_i == len(prefix):
        # for i, (_, constant) in enumerate(prefix):
        #     assert(collapsed.states[state_index].constants[assignment[i]] == constant)
        x = collapsed.get(state_index, assignment)
        v = z3.Bool("M"+str(x))
        #polarity是判断极性
        polarity = state.isPositive or ignore_label
        vars.add(x, polarity)
        return v if polarity else z3.Not(v)
    else:
        (is_forall, sort) = prefix[prefix_i]
        formulas = []
        for elem in state.constants[sort]:
            f = formula_for_state(state_index, assignment + [elem], prefix_i+1, prefix, collapsed,vars,ignore_label=ignore_label)
            formulas.append(f)
        if is_forall == (state.isPositive or ignore_label):
            return z3.And(*formulas)
        else:
            return z3.Or(*formulas)


class Separator(object):
    def __init__(self):
        self.typechecker = TypeChecker()
        self.collapsed_pool = CollapseCache()
        self.states: List[State] = []
        self.prefixes: List[List[QuantifierStr]] = [[]]
        self.prefix_index = 0
    def load(self,typechecker):
        self.typechecker = copy.deepcopy(typechecker)
    def add_state(self, state: State) -> int:
        i = len(self.states)
        self.states.append(state)
        self.collapsed_pool.add_state(state)
        return i

    def separate(self,pos_states,neg_states,imp_states,max_depth: int = 1000000, max_clauses: int = 10, max_complexity: int = 1):
        solver = z3.Solver()
        while True:
            if self.prefix_index == len(self.prefixes):
                # We have reached our maximum depth, don't generate larger prefixes
                if len(self.prefixes[0]) == max_depth:
                    return None
                self.prefixes = [[(is_forall, s)]+p for is_forall in [True, False]
                                 for p in self.prefixes for s in sorted(self.typechecker.constants.keys())]
                self.prefixes = [p for p in self.prefixes if not prefix_is_redundant(p)]
                self.prefix_index = 0
            p = self.prefixes[self.prefix_index]
            if not prefix_is_redundant(p):
                print ("Prefix:", " ".join([("∀" if is_forall else "∃") + sort + "." for (is_forall, sort) in p]))
                c = self.check_prefix_build_matrix(pos_states, neg_states, imp_states, p, solver)
                if c is not None:
                    return c
            self.prefix_index += 1
    def check_prefix_build_matrix(self, pos, neg, imp,prefix, solver: z3.Solver):
        solver.push()
        vars = VarSet()
        formulas = []
        for s_index in range(len(self.states)):
            formulas.append(z3.Bool(f"v{s_index}") == formula_for_state(s_index, [], 0, prefix, self.collapsed_pool,vars,ignore_label=True))

        for po in pos:
            formulas.append(z3.Bool(f"v{po}"))
        for n in neg:
            formulas.append(z3.Not(z3.Bool(f"v{n}")))
        for (aa, bb) in imp:
            formulas.append(z3.Implies(z3.Bool(f"v{aa}"), z3.Bool(f"v{bb}")))

        sat_formula = z3.And(formulas)
        print("There are ", len(vars.pos.symmetric_difference(vars.neg)), "pure variables of", len(vars.vars))

        solver.add(sat_formula)
        result = solver.check()
        if result == z3.unsat:
            solver.pop()
            return None
        elif result == z3.sat:
            print(solver)
            print(solver.model())
            solver.pop()
            tc_with_bv = copy.deepcopy(self.typechecker)
            for i, (_, constant) in enumerate(prefix):
                #assert "x_" + str(i) not in tc_with_bv.constants[constant]
                tc_with_bv.created_const[constant].append("x_" + str(i))

            concrete_states = {}
            for x in vars:
                concrete_states[x] = self.collapsed_pool.get_concrete(x)
            matrix = infer_matrix(concrete_states, tc_with_bv, sat_formula)
            if matrix is None:
                return None
            # checker = z3.Solver()
            # checker.add(sat_formula)NO
            # for x, m in concrete_states.items():
            #     print(check(matrix, m))
            #     checker.add(z3.Bool('M' + str(x)) if check(matrix, m) else z3.Not(z3.Bool('M' + str(x))))
            # if checker.check() != z3.sat:
            #     raise RuntimeError("Incorrect matrix!")
            return build_prefix_formula(prefix,matrix)
        else:
            assert False and "Error, z3 returned unknown"

def prefix_is_redundant(prefix: List[QuantifierStr]) -> bool:
    if len(prefix) == 0: return False
    for i in range(len(prefix) - 1):
        a,b = prefix[i], prefix[i+1]
        if a[0] == b[0] and a[1] > b[1]:
            return True
    return False

def build_prefix_formula(prefix: List[QuantifierStr], f: str, n: int = 0):
    if len(prefix) == 0:
        return f
    (is_forall, sort) = prefix[0]
    if is_forall:
        return "\A" + " x_" + str(n) + " \in Node : " + build_prefix_formula(prefix[1:], f, n + 1)
    else:
        return "\E" + " x_" +  str(n) + " \in Node : " + build_prefix_formula(prefix[1:], f, n + 1)
