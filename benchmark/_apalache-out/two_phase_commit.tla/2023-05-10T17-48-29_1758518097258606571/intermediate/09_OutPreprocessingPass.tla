------------------------ MODULE 09_OutPreprocessingPass ------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC, Apalache

CONSTANT
  (*
    @type: Set(NODE);
  *)
  Node

VARIABLE
  (*
    @type: Set(NODE);
  *)
  vote_yes

VARIABLE
  (*
    @type: Bool;
  *)
  abort_flag

VARIABLE
  (*
    @type: Set(NODE);
  *)
  go_abort

VARIABLE
  (*
    @type: Set(NODE);
  *)
  vote_no

VARIABLE
  (*
    @type: Set(NODE);
  *)
  alive

VARIABLE
  (*
    @type: Set(NODE);
  *)
  decide_abort

VARIABLE
  (*
    @type: Set(NODE);
  *)
  decide_commit

VARIABLE
  (*
    @type: Set(NODE);
  *)
  go_commit

(*
  @type: (() => Bool);
*)
Init ==
  vote_yes = {}
    /\ vote_no = {}
    /\ alive = Node
    /\ go_commit = {}
    /\ go_abort = {}
    /\ decide_commit = {}
    /\ decide_abort = {}
    /\ abort_flag = FALSE

(*
  @type: (() => Bool);
*)
InitializeNODE == Node = { "n1_OF_NODE", "n2_OF_NODE" }

(*
  @type: (() => Bool);
*)
Next ==
  (\E n$1 \in Node:
      n$1 \in alive
        /\ ~(n$1 \in vote_no)
        /\ ~(n$1 \in decide_commit)
        /\ ~(n$1 \in decide_abort)
        /\ vote_yes' = vote_yes \union {n$1}
        /\ (vote_no' := vote_no
          /\ alive' := alive
          /\ go_commit' := go_commit
          /\ go_abort' := go_abort
          /\ decide_commit' := decide_commit
          /\ decide_abort' := decide_abort
          /\ abort_flag' := abort_flag))
    \/ (\E n$2 \in Node:
      n$2 \in alive
        /\ ~(n$2 \in vote_yes)
        /\ ~(n$2 \in decide_commit)
        /\ ~(n$2 \in decide_abort)
        /\ vote_no' = vote_no \union {n$2}
        /\ abort_flag' = TRUE
        /\ decide_abort' = decide_abort \union {n$2}
        /\ (vote_yes' := vote_yes
          /\ alive' := alive
          /\ go_commit' := go_commit
          /\ go_abort' := go_abort
          /\ decide_commit' := decide_commit))
    \/ (\E n$3 \in Node:
      n$3 \in alive
        /\ alive' = { t_1$1 \in alive: ~(t_1$1 \in {n$3}) }
        /\ abort_flag' = TRUE
        /\ (vote_yes' := vote_yes
          /\ vote_no' := vote_no
          /\ go_commit' := go_commit
          /\ go_abort' := go_abort
          /\ decide_commit' := decide_commit
          /\ decide_abort' := decide_abort))
    \/ ((\A n$4 \in Node: ~(n$4 \in go_commit))
      /\ (\A n$5 \in Node: ~(n$5 \in go_abort))
      /\ (\A n$6 \in Node: n$6 \in vote_yes)
      /\ go_commit' = Node
      /\ (vote_yes' := vote_yes
        /\ vote_no' := vote_no
        /\ alive' := alive
        /\ go_abort' := go_abort
        /\ decide_commit' := decide_commit
        /\ decide_abort' := decide_abort
        /\ abort_flag' := abort_flag))
    \/ ((\A n$7 \in Node: ~(n$7 \in go_commit))
      /\ (\A n$8 \in Node: ~(n$8 \in go_abort))
      /\ (\E n$9 \in Node: n$9 \in vote_no \/ ~(n$9 \in alive))
      /\ go_abort' = Node
      /\ (vote_yes' := vote_yes
        /\ vote_no' := vote_no
        /\ alive' := alive
        /\ go_commit' := go_commit
        /\ decide_commit' := decide_commit
        /\ decide_abort' := decide_abort
        /\ abort_flag' := abort_flag))
    \/ (\E n$10 \in Node:
      n$10 \in alive
        /\ n$10 \in go_commit
        /\ decide_commit' = decide_commit \union {n$10}
        /\ (vote_yes' := vote_yes
          /\ vote_no' := vote_no
          /\ alive' := alive
          /\ go_commit' := go_commit
          /\ go_abort' := go_abort
          /\ decide_abort' := decide_abort
          /\ abort_flag' := abort_flag))
    \/ (\E n$11 \in Node:
      n$11 \in alive
        /\ n$11 \in go_abort
        /\ decide_abort' = decide_abort \union {n$11}
        /\ (vote_yes' := vote_yes
          /\ vote_no' := vote_no
          /\ alive' := alive
          /\ go_commit' := go_commit
          /\ go_abort' := go_abort
          /\ decide_commit' := decide_commit
          /\ abort_flag' := abort_flag))

(*
  @type: (() => Bool);
*)
P ==
  (vote_yes \in SUBSET Node
      /\ vote_no \in SUBSET Node
      /\ alive \in SUBSET Node
      /\ go_commit \in SUBSET Node
      /\ go_abort \in SUBSET Node
      /\ decide_commit \in SUBSET Node
      /\ decide_abort \in SUBSET Node
      /\ abort_flag \in BOOLEAN)
    /\ ((\A n$12 \in Node:
        \A n2$1 \in Node: ~(n$12 \in decide_commit) \/ ~(n2$1 \in decide_abort))
      /\ (\A n$13 \in Node:
        \A n2$2 \in Node: ~(n$13 \in decide_commit) \/ n2$2 \in vote_yes)
      /\ (\A n$14 \in Node:
        \A n2$3 \in Node: ~(n$14 \in decide_abort) \/ abort_flag))

InitializeNODEPrimed == Node' = { "n1_OF_NODE", "n2_OF_NODE" }

InitPrimed ==
  vote_yes' = {}
    /\ vote_no' = {}
    /\ alive' = Node
    /\ go_commit' = {}
    /\ go_abort' = {}
    /\ decide_commit' = {}
    /\ decide_abort' = {}
    /\ abort_flag' = FALSE

(*
  @type: Bool;
*)
VCInv_si_0 == vote_yes \in SUBSET Node

(*
  @type: Bool;
*)
VCNotInv_si_0 == ~(vote_yes \in SUBSET Node)

(*
  @type: Bool;
*)
VCInv_si_1 == vote_no \in SUBSET Node

(*
  @type: Bool;
*)
VCNotInv_si_1 == ~(vote_no \in SUBSET Node)

(*
  @type: Bool;
*)
VCInv_si_2 == alive \in SUBSET Node

(*
  @type: Bool;
*)
VCNotInv_si_2 == ~(alive \in SUBSET Node)

(*
  @type: Bool;
*)
VCInv_si_3 == go_commit \in SUBSET Node

(*
  @type: Bool;
*)
VCNotInv_si_3 == ~(go_commit \in SUBSET Node)

(*
  @type: Bool;
*)
VCInv_si_4 == go_abort \in SUBSET Node

(*
  @type: Bool;
*)
VCNotInv_si_4 == ~(go_abort \in SUBSET Node)

(*
  @type: Bool;
*)
VCInv_si_5 == decide_commit \in SUBSET Node

(*
  @type: Bool;
*)
VCNotInv_si_5 == ~(decide_commit \in SUBSET Node)

(*
  @type: Bool;
*)
VCInv_si_6 == decide_abort \in SUBSET Node

(*
  @type: Bool;
*)
VCNotInv_si_6 == ~(decide_abort \in SUBSET Node)

(*
  @type: Bool;
*)
VCInv_si_7 == abort_flag \in BOOLEAN

(*
  @type: Bool;
*)
VCNotInv_si_7 == ~(abort_flag \in BOOLEAN)

(*
  @type: Bool;
*)
VCInv_si_8 ==
  \A n$15 \in Node:
    \A n2$4 \in Node: ~(n$15 \in decide_commit) \/ ~(n2$4 \in decide_abort)

(*
  @type: Bool;
*)
VCNotInv_si_8 ==
  \E n$16 \in Node:
    \E n2$5 \in Node: n$16 \in decide_commit /\ n2$5 \in decide_abort

(*
  @type: Bool;
*)
VCInv_si_9 ==
  \A n$17 \in Node:
    \A n2$6 \in Node: ~(n$17 \in decide_commit) \/ n2$6 \in vote_yes

(*
  @type: Bool;
*)
VCNotInv_si_9 ==
  \E n$18 \in Node:
    \E n2$7 \in Node: n$18 \in decide_commit /\ ~(n2$7 \in vote_yes)

(*
  @type: Bool;
*)
VCInv_si_10 ==
  \A n$19 \in Node: \A n2$8 \in Node: ~(n$19 \in decide_abort) \/ abort_flag

(*
  @type: Bool;
*)
VCNotInv_si_10 ==
  \E n$20 \in Node: \E n2$9 \in Node: n$20 \in decide_abort /\ ~abort_flag

================================================================================
