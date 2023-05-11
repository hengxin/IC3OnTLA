# Copyright 2020 Stanford University

# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at

#     http://www.apache.org/licenses/LICENSE-2.0

# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import itertools, copy, sys
from array import array
import re
import z3
from src.separator.logic import State
from typing import List, Dict, Optional, Sequence, Iterable, Tuple, Generator
from src.typecheck import TypeChecker
K_function_unrolling = 1


# models is a map from name (eg M134) to model. sat_formula is a formula that
# uses the variables Mi, and should be made true by the resulting formula.
# sat_formula must be satisfiable, but may potentially have many satisfying
# assignments that must be explored to find a good generalizable matrix formula.
def infer_matrix(states: Dict[int, State], typechecker: TypeChecker , sat_formula: z3.ExprRef,
                 N_clauses: int = 10) :
    #trivial = trivial_check(sat_formula, states.keys())
    # if trivial is not None:
    #     return trivial

    print("Computing atom-state matrix")
    state_positions = dict((state_id, i) for (i, state_id) in enumerate(states.keys()))
    for a in atoms(typechecker):
        print(a)
    atom_model_matrix = [(array('b', (check(a, m) for m in states.values())), a) for a in atoms(typechecker)]
    atom_model_matrix_reduced = [(row, atom) for (row, atom) in atom_model_matrix if
                                 not (all(row) or all(not x for x in row))]
    atom_model_matrix_reduced.sort()
    print(atom_model_matrix_reduced)
    for i in range(len(atom_model_matrix_reduced) - 1, 1, -1):
        (r1, _), (r2, _) = atom_model_matrix_reduced[i - 1], atom_model_matrix_reduced[i]
        if r1 == r2:
            del atom_model_matrix_reduced[i]

    print("Retained", len(atom_model_matrix), "of", len(atom_model_matrix), "atoms")
    print("Have", len(states), "distinct FO-types/models")
    print("\n".join(["".join('1' if x else '0' for x in row) + " " + str(atom) for (row, atom) in atom_model_matrix]))
    print(sat_formula)
    print(states.keys())

    m = compute_minimal_with_z3_maxsat(atom_model_matrix_reduced, state_positions, sat_formula, N_clauses)
    return m


def trivial_check(sat_formula: z3.ExprRef, vars: Iterable[int]):
    s = z3.Solver()
    s.add(sat_formula)
    if s.check(*[z3.Bool('M' + str(x)) for x in vars]) == z3.sat:
        return "/\\"
    if s.check(*[z3.Not(z3.Bool('M' + str(x))) for x in vars]) == z3.sat:
        return "\/"
    return None

def atoms(typechecker:TypeChecker) -> Iterable[str]:
    vars = ""
    for key in typechecker.created_const.keys():
        for value in typechecker.created_const[key]:
            vars += value+","
    vars = vars.strip(",")
    for key in typechecker.sorts.keys():
        if len(typechecker.sorts[key]) == 0:
            yield "(" + str(key) + "= {}"+")"
        else:
            yield "(" +  vars + " \in " + str(key) + ")"
    for key in typechecker.records_set.keys():
        elems = []
        for value in typechecker.records_set[key]:
            record = value.split(",")
            if record[1] in elems:
                continue
            else:
                elems.append(record[1])
                yield "("+str(key)+"["+vars+"] = \"" + record[1] + "\")"

def check(formula: str, state: State) -> bool:
    formula = formula.strip("(")
    formula = formula.strip(")")
    if re.search(r"\\in",formula) is not None:
        value = formula.split(" \\in ")[1]
        key = formula.split(" \\in ")[0]
        if key not in state.trans_constants.keys():
            return False
        else:
            key = state.trans_constants[key]
        if len(state.sorts[value]) == 0:
            return False
        else:
            if key in state.sorts[value]:
                return True
            else:
                return False
    if re.search(r" = ",formula) is not None:
        element = formula.split(" = ")
        key = element[0]
        value = element[1].strip("\"")
        i = 0
        while key[i]!="[":
            i+=1
        key1 = key[0:i]
        j = i
        while key[j]!="]":
            j+=1
        elem = key[i+1:j]
        if elem not in state.trans_constants.keys():
            return False
        else:
            elem = state.trans_constants[elem]
        if elem in state.records[key1].keys():
            if value == state.records[key1][elem]:
                return True
            else:
                return False
        else:
            return False
    return False


def compute_minimal_with_z3_maxsat(M: List[Tuple[array, str]], state_positions: Dict[int, int],
                                   sat_formula: z3.ExprRef, N_clauses: int):
    solver = z3.Optimize()
    B = z3.Bool
    solver.add(sat_formula)
    p_terms = [[B("xp{}_{}".format(i, j)) for j in range(len(M))] for i in range(N_clauses)]
    n_terms = [[B("xn{}_{}".format(i, j)) for j in range(len(M))] for i in range(N_clauses)]
    print("Encoding model constraints")
    for x, m_index in state_positions.items():
        definition = []
        for i in range(N_clauses):
            clause = [(p_terms[i][j] if row[m_index] else n_terms[i][j]) for j, (row, _) in enumerate(M)]
            definition.append(z3.Or(*clause))
        solver.add(B("M" + str(x)) == z3.And(*definition))
    # A clause may not have both positive and negative instances of an atom
    print("Adding disjunction exclusions")
    for i in range(N_clauses):
        for j in range(len(M)):
            solver.add(z3.Or(z3.Not(B("xp{}_{}".format(i, j))),
                             z3.Not(B("xn{}_{}".format(i, j)))))

    for j in range(len(M)):
        # minimize number of atoms
        #solver.add_soft(z3.Not(z3.Or(*[B("{}{}_{}".format(p, i, j)) for i in range(N_clauses) for p in ["xp", "xn"]])))

        # minimize number of literals
        solver.add_soft(z3.Not(z3.Or(*[B("{}{}_{}".format('xp', i, j)) for i in range(N_clauses)])))
        solver.add_soft(z3.Not(z3.Or(*[B("{}{}_{}".format('xn', i, j)) for i in range(N_clauses)])))
    print("Constructed minimization problem")
    r = solver.check()
    if r == z3.sat:
        print("Found a formula")
        assignment = solver.model()
        f = []
        used = set()
        for i in range(N_clauses):
            cl = []
            for j, (row, atom) in enumerate(M):
                if assignment[B("xp{}_{}".format(i, j))]:
                    cl.append(atom)
                    used.add(j)
                elif assignment[B("xn{}_{}".format(i, j))]:
                    cl.append(("~"+atom))
                    used.add(j)
            cl.sort()
            endstr1 = ""
            for i in cl:
                endstr1 += i+"\/"
            endstr1 = endstr1.strip("\/")
            f.append(endstr1)
        print("Used", len(used), "distinct atoms")
        f.sort()
        f_minimal: List[str] = []
        for clause2 in f:
            if len(f_minimal) > 0 and f_minimal[-1] == clause2:
                continue
            f_minimal.append(clause2)
        endstr2 = ""
        for i in f_minimal:
            endstr2 += "("+i+")" + "/\\"
        endstr2 = endstr2.strip("/\\")
        return endstr2
    else:
        print(f"Z3 could not solve max-SAT problem ({r})")
        return None