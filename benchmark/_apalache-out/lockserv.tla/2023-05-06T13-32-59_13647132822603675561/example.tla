---------------------------- MODULE counterexample ----------------------------

EXTENDS lockserv

(* Constant initialization state *)
ConstInit == Node = { "n1_OF_NODE", "n2_OF_NODE", "n3_OF_NODE" }

(* Initial state *)
State0 ==
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

(* Transition 0 to State1 *)
State1 ==
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

(* The following formula holds true in the last state and violates the invariant *)
InvariantViolation == TRUE

================================================================================
(* Created by Apalache on Sat May 06 13:33:02 CST 2023 *)
(* https://github.com/informalsystems/apalache *)
