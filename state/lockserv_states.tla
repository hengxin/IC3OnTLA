Positive_State0 ==
  Node = { "n1_OF_NODE", "n2_OF_NODE", "n3_OF_NODE" }
    /\ grant_msg
      = SetAsFun({ <<"n1_OF_NODE", FALSE>>,
        <<"n2_OF_NODE", FALSE>>,
        <<"n3_OF_NODE", FALSE>> })
    /\ holds_lock
      = SetAsFun({ <<"n1_OF_NODE", FALSE>>,
        <<"n2_OF_NODE", FALSE>>,
        <<"n3_OF_NODE", FALSE>> })
    /\ lock_msg
      = SetAsFun({ <<"n1_OF_NODE", FALSE>>,
        <<"n2_OF_NODE", FALSE>>,
        <<"n3_OF_NODE", FALSE>> })
    /\ server_holds_lock = TRUE
    /\ unlock_msg
      = SetAsFun({ <<"n1_OF_NODE", FALSE>>,
        <<"n2_OF_NODE", FALSE>>,
        <<"n3_OF_NODE", FALSE>> })
End

Positive_State1 ==
  Node = { "n1_OF_NODE", "n2_OF_NODE", "n3_OF_NODE" }
    /\ grant_msg
      = SetAsFun({ <<"n1_OF_NODE", FALSE>>,
        <<"n2_OF_NODE", FALSE>>,
        <<"n3_OF_NODE", FALSE>> })
    /\ holds_lock
      = SetAsFun({ <<"n1_OF_NODE", FALSE>>,
        <<"n2_OF_NODE", FALSE>>,
        <<"n3_OF_NODE", FALSE>> })
    /\ lock_msg
      = SetAsFun({ <<"n1_OF_NODE", FALSE>>,
        <<"n2_OF_NODE", FALSE>>,
        <<"n3_OF_NODE", TRUE>> })
    /\ server_holds_lock = TRUE
    /\ unlock_msg
      = SetAsFun({ <<"n1_OF_NODE", FALSE>>,
        <<"n2_OF_NODE", FALSE>>,
        <<"n3_OF_NODE", FALSE>> })
End

Negative_State2 ==
  Node = { "n1_OF_NODE", "n2_OF_NODE", "n3_OF_NODE" }
    /\ grant_msg
      = SetAsFun({ <<"n1_OF_NODE", FALSE>>,
        <<"n2_OF_NODE", TRUE>>,
        <<"n3_OF_NODE", FALSE>> })
    /\ holds_lock
      = SetAsFun({ <<"n1_OF_NODE", FALSE>>,
        <<"n2_OF_NODE", FALSE>>,
        <<"n3_OF_NODE", TRUE>> })
    /\ lock_msg
      = SetAsFun({ <<"n1_OF_NODE", FALSE>>,
        <<"n2_OF_NODE", TRUE>>,
        <<"n3_OF_NODE", FALSE>> })
    /\ server_holds_lock = TRUE
    /\ unlock_msg
      = SetAsFun({ <<"n1_OF_NODE", FALSE>>,
        <<"n2_OF_NODE", FALSE>>,
        <<"n3_OF_NODE", FALSE>> })
End

Negative_State3 ==
  Node = { "n1_OF_NODE", "n2_OF_NODE", "n3_OF_NODE" }
    /\ grant_msg
      = SetAsFun({ <<"n1_OF_NODE", FALSE>>,
        <<"n2_OF_NODE", FALSE>>,
        <<"n3_OF_NODE", FALSE>> })
    /\ holds_lock
      = SetAsFun({ <<"n1_OF_NODE", FALSE>>,
        <<"n2_OF_NODE", TRUE>>,
        <<"n3_OF_NODE", TRUE>> })
    /\ lock_msg
      = SetAsFun({ <<"n1_OF_NODE", FALSE>>,
        <<"n2_OF_NODE", TRUE>>,
        <<"n3_OF_NODE", FALSE>> })
    /\ server_holds_lock = TRUE
    /\ unlock_msg
      = SetAsFun({ <<"n1_OF_NODE", FALSE>>,
        <<"n2_OF_NODE", FALSE>>,
        <<"n3_OF_NODE", FALSE>> })
End