---------------------------- MODULE counterexample ----------------------------

EXTENDS peterson

(* Constant initialization state *)
ConstInit == ProcSet = { "p0_OF_PROCSET", "p1_OF_PROCSET" }

(* Initial state *)
State0 ==
  ProcSet = { "p0_OF_PROCSET", "p1_OF_PROCSET" }
    /\ flag
      = SetAsFun({ <<"p0_OF_PROCSET", FALSE>>, <<"p1_OF_PROCSET", FALSE>> })
    /\ pc = SetAsFun({ <<"p0_OF_PROCSET", "cs">>, <<"p1_OF_PROCSET", "a4">> })
    /\ turn = "p0_OF_PROCSET"

(* Transition 4 to State1 *)
State1 ==
  ProcSet = { "p0_OF_PROCSET", "p1_OF_PROCSET" }
    /\ flag
      = SetAsFun({ <<"p0_OF_PROCSET", FALSE>>, <<"p1_OF_PROCSET", FALSE>> })
    /\ pc = SetAsFun({ <<"p0_OF_PROCSET", "cs">>, <<"p1_OF_PROCSET", "cs">> })
    /\ turn = "p0_OF_PROCSET"

(* The following formula holds true in the last state and violates the invariant *)
InvariantViolation ==
  Skolem((\E p$3 \in ProcSet:
    Skolem((\E q$3 \in ProcSet:
      ~(p$3 = q$3) /\ (pc[p$3] = "cs" /\ pc[q$3] = "cs")))))

================================================================================
(* Created by Apalache on Sat May 06 13:21:20 CST 2023 *)
(* https://github.com/informalsystems/apalache *)
