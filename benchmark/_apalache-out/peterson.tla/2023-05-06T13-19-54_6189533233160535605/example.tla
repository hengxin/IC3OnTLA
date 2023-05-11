---------------------------- MODULE counterexample ----------------------------

EXTENDS peterson

(* Constant initialization state *)
ConstInit == ProcSet = { "p0_OF_PROCSET", "p1_OF_PROCSET" }

(* Initial state *)
State0 ==
  ProcSet = { "p0_OF_PROCSET", "p1_OF_PROCSET" }
    /\ flag
      = SetAsFun({ <<"p0_OF_PROCSET", FALSE>>, <<"p1_OF_PROCSET", FALSE>> })
    /\ pc = SetAsFun({ <<"p0_OF_PROCSET", "a1">>, <<"p1_OF_PROCSET", "a1">> })
    /\ turn = "p1_OF_PROCSET"

(* Transition 3 to State1 *)
State1 ==
  ProcSet = { "p0_OF_PROCSET", "p1_OF_PROCSET" }
    /\ flag
      = SetAsFun({ <<"p0_OF_PROCSET", FALSE>>, <<"p1_OF_PROCSET", FALSE>> })
    /\ pc = SetAsFun({ <<"p0_OF_PROCSET", "a2">>, <<"p1_OF_PROCSET", "a1">> })
    /\ turn = "p1_OF_PROCSET"

(* The following formula holds true in the last state and violates the invariant *)
InvariantViolation == TRUE

================================================================================
(* Created by Apalache on Sat May 06 13:19:57 CST 2023 *)
(* https://github.com/informalsystems/apalache *)
