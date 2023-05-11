# This is a simplified and incomplete python version of IC3 code based on First-Order Quantified Separators
# It is not intended to be executable or correct, but only to illustrate the main idea of the algorithm
# The code is adapted from the pseudocode in Figure 7 of the paper [1]

# Assume we have a first-order transition system T = (I, R) where I is the initial states and R is the transition relation
# Assume we have a safety property P to be checked
# Assume we have a separation oracle that can find a separator for a given set of positive and negative structures
# Assume we have a first-order solver that can check satisfiability and validity of first-order formulas
from src.separator import separate
import apalachecheck
import write2spec
import typecheck
from src.separator import logic
from typing import List

inv_index = 0
state_index = 0
def FOL_IC3(spec):
  global state_index
  pos_states = []
  neg_states = []
  #spec = "two_phase_commit"
  #create a frame
  F = [[]]
  # Initialize frames F0, F1, ..., Fn as conjunctions of formulas
  F[0] = ["Init"] # F0 is the initial states
  n = 1 # n is the number of frames
  def PropagationClause(state_index,pos_states) -> None:
    F.append([])
    F[-1].append("True_Formula")
    F[-1].append("TypeOK")
    for i in range(0,len(F)-1):
      for lemma in F[i]:
        # check is_sat(F[i] & R & lemma => lemma)
        check_inv = "need_check_inv == "+conjuction(F[i]) +"\n"
        write2spec.del_the_last_one()
        write2spec.write_new_inv_to_spec(check_inv)
        write2spec.write_new_inv_to_spec("=========")
        result = apalachecheck.apalache_check_inv(spec, "need_check_inv", lemma, "InitializeNode", 1,state_index)
        if result[0]:
          # Lemma can be pushed to next frame
          F[i+1].append(lemma)
          for j in range(state_index,result[1]):
            pos_states.append(j)
          state_index = result[1]
          print(str(i+1)+":"+conjuction(F[i+1]))
        write2spec.del_the_last_one()
        write2spec.del_the_last_one()
        write2spec.write_new_inv_to_spec("=========")
    return pos_states,state_index


  def check_inductive():
    for i in range(n+1):
      check_inv = "need_check_inv == " + conjuction(F[i]) +"/\ Safety"+ "\n"
      write2spec.del_the_last_one()
      write2spec.write_new_inv_to_spec(check_inv)
      write2spec.write_new_inv_to_spec("=========")
      result = apalachecheck.apalache_check_inductive(spec, "need_check_inv", "need_check_inv", "InitializeNode", 1)
      write2spec.del_the_last_one()
      write2spec.del_the_last_one()
      write2spec.write_new_inv_to_spec("=========")
      if result:
        return i
    return None


  def check_safe(Frame,state_index,neg_states):
    print("find bad_state")
    check_inv = "need_check_inv == " + conjuction(Frame)  + "\n"
    write2spec.del_the_last_one()
    write2spec.write_new_inv_to_spec(check_inv)
    write2spec.write_new_inv_to_spec("=========")
    result = apalachecheck.apalache_check_safe(spec, "need_check_inv", "P", "InitializeNode", 0,state_index)
    write2spec.del_the_last_one()
    write2spec.del_the_last_one()
    write2spec.write_new_inv_to_spec("=========")
    if result[0]:
      print("no bad_state")
      return neg_states,state_index,result[2]
    else:
      for i in range(state_index,result[1]):
        neg_states.append(i)
      state_index = result[1]
      print("have bad_state")
      return neg_states,state_index,result[2]


  def block(bad_state,n,bad_state_index):
    print("need block state is :"+ bad_state)
    print(pos_states)
    print(neg_states)
    global state_index
    global inv_index
    if n == 0:
      return False
    while True:
      print("check F[i-1] /\ ~s /\ T -> s")
      print("Fn:" + conjuction(F[n]))
      print("Fn-1:" + conjuction(F[n-1]))
      check_inv_1 = "check_inv_1 == " + bad_state.replace("\n", "") + "\n"
      check_inv_0 = "check_inv_0 == "+ conjuction(F[n-1])+ "/\\" + "~(check_inv_1)"+"\n"
      write2spec.del_the_last_one()
      write2spec.write_new_inv_to_spec(check_inv_1)
      write2spec.write_new_inv_to_spec(check_inv_0)
      write2spec.write_new_inv_to_spec("=========")
      result = apalachecheck.apalache_check_sat_state("two_phase_commit","check_inv_0","check_inv_1","InitializeNode",1,state_index)
      write2spec.del_the_last_one()
      write2spec.del_the_last_one()
      write2spec.del_the_last_one()
      write2spec.write_new_inv_to_spec("=========")
      print(result)
      if result[0]:
        #获取前继进行block
        for i in range(state_index,result[1]):
          neg_states.append(i)
        state_index = result[1]
        pre_state = result[2]
        block(pre_state,n-1,state_index-1)
      else:
        break
    typechecker = typecheck.TypeChecker()
    typechecker.typecheck()
    separator = separate.Separator()
    separator.load(typechecker)
    separator.collapsed_pool.load(typechecker)
    print(pos_states)
    print(neg_states)
    index = 0
    pos_states_sep = []
    neg_states_sep = []
    for i in range(0,state_index):
      if i in pos_states:
        state = logic.State()
        state.load(typechecker)
        state.update(True, i, "two_phase_commit")
        separator.add_state(state)
        pos_states_sep.append(index)
        index += 1
      elif i in neg_states:
        state = logic.State()
        state.load(typechecker)
        state.update(False, i, "two_phase_commit")
        separator.add_state(state)
        neg_states_sep.append(index)
        index += 1
      else:
        continue
    print(pos_states_sep)
    print(neg_states_sep)
    p = separator.separate(pos_states_sep, neg_states_sep, [], 5, 3)
    if p is None:
      return False
    else:
      check_inv = "inv_" + str(inv_index) +  " == "  + p + "\n"
      write2spec.del_the_last_one()
      write2spec.write_new_inv_to_spec(check_inv)
      write2spec.write_new_inv_to_spec("=========")
      print("Find a formula"+p)
      print("check init -> p")
      result = apalachecheck.apalache_check_init("two_phase_commit","Init","inv_" + str(inv_index),"InitializeNode",0)
      print(result)
      inv_index += 1
      if result:
        print("check fi-1 /\ p -> wp(p)")
        check_inv = "need_check_inv == " + conjuction(F[n-1]) + " /\\ "+"inv_"+str(inv_index-1) + "\n"
        write2spec.del_the_last_one()
        write2spec.write_new_inv_to_spec(check_inv)
        write2spec.write_new_inv_to_spec("=========")
        result = apalachecheck.apalache_check_inductive_relative("two_phase_commit","need_check_inv","inv_" + str(inv_index-1),"InitializeNode",1,state_index)
        write2spec.del_the_last_one()
        write2spec.del_the_last_one()
        write2spec.write_new_inv_to_spec("=========")
        print(result)
        if result[0]:
          print("inv_"+str(inv_index-1)+"is a good formula")
          for i in range(0,n+1):
            F[i].append("inv_"+str(inv_index-1))
          for i in bad_state_index:
            neg_states.remove(i)
        else:
          for i in range(state_index,result[1]):
            neg_states.append(i)
          state_index = result[1]
          bad_state_index.append(state_index-1)
          return block(bad_state,n,bad_state_index)
      else:
        return False
    return True

  # Check if F1(FO/Init) implies P
  # is_sat(F[1]=>P)
  # result = apalachecheck.apalache_check_sat(spec, "Init", "P","InitializeNode" ,0,state_index)
  # if not result[0]:
  #   # Counterexample found in F0
  #   #need write positive state to states
  #   return False
  # for i in range(state_index,result[1]):
  #   pos_states.append(i)
  # state_index = result[1]
  result = apalachecheck.apalache_check_sat(spec, "Init", "P", "InitializeNode", 1, state_index)
  if not result[0]:
    # Counterexample found in F0
    # need write positive state to states
    return False
  for i in range(state_index,result[1]):
    pos_states.append(i)
  state_index = result[1]
  pos_states, state_index = PropagationClause(state_index, pos_states)
  while True:
    # Check if Fn is inductive (we have already checked Init => Fn)
    # is_sat(F[n] & R => F[n])

    while True:
      neg_states,state_index,bad_state = check_safe(F[n],state_index,neg_states)
      if bad_state is None:
        break
      else:
        bad_state_list = []
        bad_state_list.append(state_index-1)
        if not block(bad_state,n,bad_state_list):
          return False
    print("push")
    pos_states, state_index = PropagationClause(state_index, pos_states)
    n+=1
    result = check_inductive()
    if result is not None:
      print(conjuction(F[result]))
      return conjuction(F[result])

def conjuction(Fn):
  str = Fn[0]
  for i in range(1,len(Fn)):
    str = str + "/\\" + Fn[i]
  return str
