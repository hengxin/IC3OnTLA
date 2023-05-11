---------------------------- MODULE counterexample ----------------------------

EXTENDS two_phase_commit

(* Constant initialization state *)
ConstInit == Node = { "n1_OF_NODE", "n2_OF_NODE" }

(* Initial state *)
State0 ==
  Node = { "n1_OF_NODE", "n2_OF_NODE" }
    /\ abort_flag = FALSE
    /\ alive = {"n2_OF_NODE"}
    /\ decide_abort = {"n2_OF_NODE"}
    /\ decide_commit = {}
    /\ go_abort = {"n2_OF_NODE"}
    /\ go_commit = {}
    /\ vote_no = {}
    /\ vote_yes = {}

(* The following formula holds true in the last state and violates the invariant *)
InvariantViolation ==
  Skolem((\E n$17 \in Node:
    Skolem((\E n2$6 \in Node: n$17 \in decide_abort /\ ~abort_flag))))

================================================================================
(* Created by Apalache on Wed May 10 17:53:58 CST 2023 *)
(* https://github.com/informalsystems/apalache *)
