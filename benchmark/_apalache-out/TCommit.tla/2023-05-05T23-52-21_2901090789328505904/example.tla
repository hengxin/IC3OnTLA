---------------------------- MODULE counterexample ----------------------------

EXTENDS TCommit

(* Constant initialization state *)
ConstInit == RM = { "r1_OF_RM", "r2_OF_RM", "r3_OF_RM" }

(* Initial state *)
State0 ==
  RM = { "r1_OF_RM", "r2_OF_RM", "r3_OF_RM" }
    /\ rmState
      = SetAsFun({ <<"r1_OF_RM", "working">>,
        <<"r2_OF_RM", "working">>,
        <<"r3_OF_RM", "working">> })

(* Transition 2 to State1 *)
State1 ==
  RM = { "r1_OF_RM", "r2_OF_RM", "r3_OF_RM" }
    /\ rmState
      = SetAsFun({ <<"r1_OF_RM", "working">>,
        <<"r2_OF_RM", "aborted">>,
        <<"r3_OF_RM", "working">> })

(* Transition 2 to State2 *)
State2 ==
  RM = { "r1_OF_RM", "r2_OF_RM", "r3_OF_RM" }
    /\ rmState
      = SetAsFun({ <<"r1_OF_RM", "aborted">>,
        <<"r2_OF_RM", "aborted">>,
        <<"r3_OF_RM", "working">> })

(* The following formula holds true in the last state and violates the invariant *)
InvariantViolation == TRUE

================================================================================
(* Created by Apalache on Fri May 05 23:52:23 CST 2023 *)
(* https://github.com/informalsystems/apalache *)
