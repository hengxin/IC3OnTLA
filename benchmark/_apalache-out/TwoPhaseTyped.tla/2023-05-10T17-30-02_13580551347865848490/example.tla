---------------------------- MODULE counterexample ----------------------------

EXTENDS TwoPhaseTyped

(* Constant initialization state *)
ConstInit == RM = { "r1_OF_RM", "r2_OF_RM" }

(* Initial state *)
State0 ==
  RM = { "r1_OF_RM", "r2_OF_RM" }
    /\ msgs = {}
    /\ rmState
      = SetAsFun({ <<"r1_OF_RM", "working">>, <<"r2_OF_RM", "working">> })
    /\ tmPrepared = {}
    /\ tmState = "init"

(* Transition 4 to State1 *)
State1 ==
  RM = { "r1_OF_RM", "r2_OF_RM" }
    /\ msgs = {}
    /\ rmState
      = SetAsFun({ <<"r1_OF_RM", "working">>, <<"r2_OF_RM", "aborted">> })
    /\ tmPrepared = {}
    /\ tmState = "init"

(* The following formula holds true in the last state and violates the invariant *)
InvariantViolation == TRUE

================================================================================
(* Created by Apalache on Wed May 10 17:30:05 CST 2023 *)
(* https://github.com/informalsystems/apalache *)
