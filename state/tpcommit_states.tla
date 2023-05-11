Positive_State0 ==
  RM = { "r1_OF_RM", "r2_OF_RM", "r3_OF_RM" }
    /\ msgs = {}
    /\ rmState
      = SetAsFun({ <<"r1_OF_RM", "working">>,
        <<"r2_OF_RM", "working">>,
        <<"r3_OF_RM", "working">> })
    /\ tmPrepared = {}
    /\ tmState = "init"
End

Positive_State1 ==
  RM = { "r1_OF_RM", "r2_OF_RM", "r3_OF_RM" }
    /\ msgs = {}
    /\ rmState
      = SetAsFun({ <<"r1_OF_RM", "aborted">>,
        <<"r2_OF_RM", "working">>,
        <<"r3_OF_RM", "working">> })
    /\ tmPrepared = {}
    /\ tmState = "init"
End

Positive_State2 ==
  RM = { "r1_OF_RM", "r2_OF_RM", "r3_OF_RM" }
    /\ rmState
      = SetAsFun({ <<"r1_OF_RM", "prepared">>,
        <<"r2_OF_RM", "working">>,
        <<"r3_OF_RM", "working">> })
    /\ tmPrepared = {}
    /\ tmState = "init"
End

Positive_State3 ==
  RM = { "r1_OF_RM", "r2_OF_RM", "r3_OF_RM" }
    /\ msgs = {}
    /\ rmState
      = SetAsFun({ <<"r1_OF_RM", "prepared">>,
        <<"r2_OF_RM", "working">>,
        <<"r3_OF_RM", "working">> })
    /\ tmPrepared = {"r1_OF_RM"}
    /\ tmState = "init"
End

Negative_State4 ==
  RM = { "r1_OF_RM", "r2_OF_RM", "r3_OF_RM" }
    /\ msgs = {[type |-> "Commit"]}
    /\ rmState
      = SetAsFun({ <<"r1_OF_RM", "prepared">>,
        <<"r2_OF_RM", "aborted">>,
        <<"r3_OF_RM", "committed">> })
    /\ tmPrepared = { "r1_OF_RM", "r2_OF_RM", "r3_OF_RM" }
    /\ tmState = "init"
End

Negative_State5 ==
  RM = { "r1_OF_RM", "r2_OF_RM", "r3_OF_RM" }
    /\ msgs = {[type |-> "Commit"]}
    /\ rmState
      = SetAsFun({ <<"r1_OF_RM", "prepared">>,
        <<"r2_OF_RM", "aborted">>,
        <<"r3_OF_RM", "prepared">> })
    /\ tmPrepared = { "r1_OF_RM", "r2_OF_RM", "r3_OF_RM" }
    /\ tmState = "init"
End
