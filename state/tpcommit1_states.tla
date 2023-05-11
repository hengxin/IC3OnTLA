Positive_State0 ==
  Node = { "n1_OF_NODE", "n2_OF_NODE", "n3_OF_NODE" }
    /\ alive = { "n1_OF_NODE", "n3_OF_NODE" }
    /\ decide_abort = {}
    /\ decide_commit = {}
    /\ go_abort = {}
    /\ go_commit = {}
    /\ vote_no = {}
    /\ vote_yes = {"n1_OF_NODE"}
End

Positive_State1 ==
  Node = { "n1_OF_NODE", "n2_OF_NODE", "n3_OF_NODE" }
    /\ alive = { "n1_OF_NODE", "n2_OF_NODE", "n3_OF_NODE" }
    /\ decide_abort = {}
    /\ decide_commit = {}
    /\ go_abort = {}
    /\ go_commit = {}
    /\ vote_no = {}
    /\ vote_yes = {}
End

Negative_State2 ==
  Node = { "n1_OF_NODE", "n2_OF_NODE", "n3_OF_NODE" }
    /\ abort_flag = FALSE
    /\ alive = {}
    /\ decide_abort = {"n3_OF_NODE"}
    /\ decide_commit = {}
    /\ go_abort = {}
    /\ go_commit = {}
    /\ vote_no = {}
    /\ vote_yes = {}
End



