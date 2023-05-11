Positive_State0 ==
  ProcSet = { "p0_OF_PROCSET", "p1_OF_PROCSET" }
    /\ flag
      = SetAsFun({ <<"p0_OF_PROCSET", FALSE>>, <<"p1_OF_PROCSET", FALSE>> })
    /\ pc = SetAsFun({ <<"p0_OF_PROCSET", "a1">>, <<"p1_OF_PROCSET", "a1">> })
    /\ turn = {"p1_OF_PROCSET"}
End

Positive_State1 ==
  ProcSet = { "p0_OF_PROCSET", "p1_OF_PROCSET" }
    /\ flag
      = SetAsFun({ <<"p0_OF_PROCSET", FALSE>>, <<"p1_OF_PROCSET", FALSE>> })
    /\ pc = SetAsFun({ <<"p0_OF_PROCSET", "a2">>, <<"p1_OF_PROCSET", "a1">> })
    /\ turn = {"p1_OF_PROCSET"}
End

Negative_State2 ==
  ProcSet = { "p0_OF_PROCSET", "p1_OF_PROCSET" }
    /\ flag
      = SetAsFun({ <<"p0_OF_PROCSET", FALSE>>, <<"p1_OF_PROCSET", FALSE>> })
    /\ pc = SetAsFun({ <<"p0_OF_PROCSET", "cs">>, <<"p1_OF_PROCSET", "a4">> })
    /\ turn = {"p0_OF_PROCSET"}
End

Negative_State3 ==
  ProcSet = { "p0_OF_PROCSET", "p1_OF_PROCSET" }
    /\ flag
      = SetAsFun({ <<"p0_OF_PROCSET", FALSE>>, <<"p1_OF_PROCSET", FALSE>> })
    /\ pc = SetAsFun({ <<"p0_OF_PROCSET", "cs">>, <<"p1_OF_PROCSET", "cs">> })
    /\ turn = {"p0_OF_PROCSET"}
End

