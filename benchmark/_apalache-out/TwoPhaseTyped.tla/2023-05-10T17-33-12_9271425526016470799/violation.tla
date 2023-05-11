---------------------------- MODULE counterexample ----------------------------

EXTENDS TwoPhaseTyped

(* Constant initialization state *)
ConstInit == RM = { "r1_OF_RM", "r2_OF_RM" }

(* Initial state *)
State0 ==
  RM = { "r1_OF_RM", "r2_OF_RM" }
    /\ msgs = {}
    /\ rmState
      = SetAsFun({ <<"r1_OF_RM", "aborted">>, <<"r2_OF_RM", "committed">> })
    /\ tmPrepared = {}
    /\ tmState = "committed"

(* The following formula holds true in the last state and violates the invariant *)
InvariantViolation ==
  Skolem((\E rm1$2 \in RM:
    Skolem((\E rm2$2 \in RM:
      rmState[rm1$2] = "aborted" /\ rmState[rm2$2] = "committed"))))

================================================================================
(* Created by Apalache on Wed May 10 17:33:14 CST 2023 *)
(* https://github.com/informalsystems/apalache *)
