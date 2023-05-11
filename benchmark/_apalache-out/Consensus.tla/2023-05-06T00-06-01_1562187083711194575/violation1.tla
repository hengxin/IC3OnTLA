---------------------------- MODULE counterexample ----------------------------

EXTENDS Consensus

(* Constant initialization state *)
ConstInit == Value = { "v1_OF_VALUE", "v2_OF_VALUE", "v3_OF_VALUE" }

(* Initial state *)
State0 == Value = { "v1_OF_VALUE", "v2_OF_VALUE", "v3_OF_VALUE" } /\ chosen = {}

(* The following formula holds true in the last state and violates the invariant *)
InvariantViolation == chosen \in SUBSET Value

================================================================================
(* Created by Apalache on Sat May 06 00:06:03 CST 2023 *)
(* https://github.com/informalsystems/apalache *)
