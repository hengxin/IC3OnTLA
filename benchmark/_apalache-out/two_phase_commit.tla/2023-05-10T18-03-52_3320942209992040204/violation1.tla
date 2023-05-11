---------------------------- MODULE counterexample ----------------------------

EXTENDS two_phase_commit

(* Constant initialization state *)
ConstInit == Node = { "n1_OF_NODE", "n2_OF_NODE" }

(* Initial state *)
State0 ==
  Node = { "n1_OF_NODE", "n2_OF_NODE" }
    /\ abort_flag = TRUE
    /\ alive = {"n2_OF_NODE"}
    /\ decide_abort = {"n2_OF_NODE"}
    /\ decide_commit = {}
    /\ go_abort = {}
    /\ go_commit = {"n2_OF_NODE"}
    /\ vote_no = {"n2_OF_NODE"}
    /\ vote_yes = { "n1_OF_NODE", "n2_OF_NODE" }

(* Transition 5 to State1 *)
State1 ==
  Node = { "n1_OF_NODE", "n2_OF_NODE" }
    /\ abort_flag = TRUE
    /\ alive = {"n2_OF_NODE"}
    /\ decide_abort = {"n2_OF_NODE"}
    /\ decide_commit = {"n2_OF_NODE"}
    /\ go_abort = {}
    /\ go_commit = {"n2_OF_NODE"}
    /\ vote_no = {"n2_OF_NODE"}
    /\ vote_yes = { "n1_OF_NODE", "n2_OF_NODE" }

(* The following formula holds true in the last state and violates the invariant *)
InvariantViolation ==
  Skolem((\E n$16 \in Node:
    Skolem((\E n2$5 \in Node: n$16 \in decide_commit /\ n2$5 \in decide_abort))))

================================================================================
(* Created by Apalache on Wed May 10 18:03:55 CST 2023 *)
(* https://github.com/informalsystems/apalache *)
