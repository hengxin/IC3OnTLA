Positive_State0 ==
  Node = { "n1_OF_NODE", "n2_OF_NODE" }
    /\ abort_flag = FALSE
    /\ alive = { "n1_OF_NODE", "n2_OF_NODE" }
    /\ decide_abort = {}
    /\ decide_commit = {}
    /\ go_abort = {}
    /\ go_commit = {}
    /\ vote_no = {}
    /\ vote_yes = {}
End

Positiive_State1 ==
  Node = { "n1_OF_NODE", "n2_OF_NODE" }
    /\ abort_flag = FALSE
    /\ alive = { "n1_OF_NODE", "n2_OF_NODE" }
    /\ decide_abort = {}
    /\ decide_commit = {}
    /\ go_abort = {}
    /\ go_commit = {}
    /\ vote_no = {}
    /\ vote_yes = {"n1_OF_NODE"}
End

Negative_State2 ==
  Node = { "n1_OF_NODE", "n2_OF_NODE" }
    /\ abort_flag = TRUE
    /\ alive = { "n1_OF_NODE", "n2_OF_NODE" }
    /\ decide_abort = {"n1_OF_NODE"}
    /\ decide_commit = {"n2_OF_NODE"}
    /\ go_abort = {}
    /\ go_commit = {"n2_OF_NODE"}
    /\ vote_no = { "n1_OF_NODE", "n2_OF_NODE" }
    /\ vote_yes = { "n1_OF_NODE", "n2_OF_NODE" }
End

