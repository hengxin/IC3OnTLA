Positive_State0 ==
  RM = { "r1_OF_RM", "r2_OF_RM" }
    /\ msgs = {}
    /\ rmState
      = SetAsFun({ <<"r1_OF_RM", "working">>, <<"r2_OF_RM", "working">> })
    /\ tmPrepared = {}
    /\ tmState = "init"
End

Positive_State1 ==
  RM = { "r1_OF_RM", "r2_OF_RM" }
    /\ msgs = {}
    /\ rmState
      = SetAsFun({ <<"r1_OF_RM", "working">>, <<"r2_OF_RM", "aborted">> })
    /\ tmPrepared = {}
    /\ tmState = "init"
End

Negative_State2 ==
  RM = { "r1_OF_RM", "r2_OF_RM" }
    /\ msgs = {}
    /\ rmState
      = SetAsFun({ <<"r1_OF_RM", "aborted">>, <<"r2_OF_RM", "committed">> })
    /\ tmPrepared = {}
    /\ tmState = "committed"
End