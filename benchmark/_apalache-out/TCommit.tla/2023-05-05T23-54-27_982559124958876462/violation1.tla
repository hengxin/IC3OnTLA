---------------------------- MODULE counterexample ----------------------------

EXTENDS TCommit

(* Constant initialization state *)
ConstInit == RM = { "r1_OF_RM", "r2_OF_RM", "r3_OF_RM" }

(* Initial state *)
State0 ==
  RM = { "r1_OF_RM", "r2_OF_RM", "r3_OF_RM" }
    /\ rmState
      = SetAsFun({ <<"r1_OF_RM", "prepared">>,
        <<"r2_OF_RM", "prepared">>,
        <<"r3_OF_RM", "working">> })

(* The following formula holds true in the last state and violates the invariant *)
InvariantViolation ==
  DOMAIN rmState = RM
    /\ (\A t_5$1 \in RM:
      rmState[t_5$1] \in { "working", "prepared", "committed", "aborted" })

================================================================================
(* Created by Apalache on Fri May 05 23:54:29 CST 2023 *)
(* https://github.com/informalsystems/apalache *)
