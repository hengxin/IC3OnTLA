---------------------------- MODULE counterexample ----------------------------

EXTENDS two_phase_commit

(* Constant initialization state *)
ConstInit == Node = { "n1_OF_NODE", "n2_OF_NODE" }

(* Initial state *)
State0 ==
  Node = { "n1_OF_NODE", "n2_OF_NODE" }
    /\ abort_flag = FALSE
    /\ alive = { "n1_OF_NODE", "n2_OF_NODE" }
    /\ decide_abort = {}
    /\ decide_commit = {}
    /\ go_abort = {}
    /\ go_commit = {}
    /\ vote_no = {}
    /\ vote_yes = {}

(* Transition 0 to State1 *)
State1 ==
  Node = { "n1_OF_NODE", "n2_OF_NODE" }
    /\ abort_flag = FALSE
    /\ alive = { "n1_OF_NODE", "n2_OF_NODE" }
    /\ decide_abort = {}
    /\ decide_commit = {}
    /\ go_abort = {}
    /\ go_commit = {}
    /\ vote_no = {}
    /\ vote_yes = {"n1_OF_NODE"}

(* The following formula holds true in the last state and violates the invariant *)
InvariantViolation == TRUE

================================================================================
(* Created by Apalache on Wed May 10 17:48:33 CST 2023 *)
(* https://github.com/informalsystems/apalache *)
