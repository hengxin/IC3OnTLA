---------------------------- MODULE counterexample ----------------------------

EXTENDS TCommit

(* Constant initialization state *)
ConstInit == RM = { "r1_OF_RM", "r2_OF_RM", "r3_OF_RM" }

(* Initial state *)
State0 ==
  RM = { "r1_OF_RM", "r2_OF_RM", "r3_OF_RM" }
    /\ rmState
      = SetAsFun({ <<"r1_OF_RM", "committed">>,
        <<"r2_OF_RM", "working">>,
        <<"r3_OF_RM", "prepared">> })

(* Transition 0 to State1 *)
State1 ==
  RM = { "r1_OF_RM", "r2_OF_RM", "r3_OF_RM" }
    /\ rmState
      = SetAsFun({ <<"r1_OF_RM", "committed">>,
        <<"r2_OF_RM", "prepared">>,
        <<"r3_OF_RM", "prepared">> })

(* The following formula holds true in the last state and violates the invariant *)
InvariantViolation == TRUE

================================================================================
(* Created by Apalache on Fri May 05 23:51:58 CST 2023 *)
(* https://github.com/informalsystems/apalache *)
