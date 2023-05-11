Positive_State0 ==
  RM = { "r1_OF_RM", "r2_OF_RM", "r3_OF_RM" }
    /\ rmState
      = SetAsFun({ <<"r1_OF_RM", "working">>,
        <<"r2_OF_RM", "working">>,
        <<"r3_OF_RM", "working">> })
End

Positive_State1 ==
  RM = { "r1_OF_RM", "r2_OF_RM", "r3_OF_RM" }
    /\ rmState
      = SetAsFun({ <<"r1_OF_RM", "prepared">>,
        <<"r2_OF_RM", "prepared">>,
        <<"r3_OF_RM", "working">> })
End

Negative_State2 ==
  RM = { "r1_OF_RM", "r2_OF_RM", "r3_OF_RM" }
    /\ rmState
      = SetAsFun({ <<"r1_OF_RM", "working">>,
        <<"r2_OF_RM", "aborted">>,
        <<"r3_OF_RM", "working">> })
End



