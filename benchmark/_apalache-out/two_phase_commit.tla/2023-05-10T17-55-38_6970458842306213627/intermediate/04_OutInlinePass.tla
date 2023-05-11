--------------------------- MODULE 04_OutInlinePass ---------------------------

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
InitializeNODE == Node = { "n1_OF_NODE", "n2_OF_NODE" }

(*
  @type: (() => Bool);
*)
Next ==
  (\E n$10 \in Node:
      n$10 \in alive
        /\ n$10 \notin vote_no
        /\ n$10 \notin decide_commit
        /\ n$10 \notin decide_abort
        /\ vote_yes' = vote_yes \union {n$10}
        /\ (vote_no' := vote_no
          /\ alive' := alive
          /\ go_commit' := go_commit
          /\ go_abort' := go_abort
          /\ decide_commit' := decide_commit
          /\ decide_abort' := decide_abort
          /\ abort_flag' := abort_flag))
    \/ (\E n$11 \in Node:
      n$11 \in alive
        /\ n$11 \notin vote_yes
        /\ n$11 \notin decide_commit
        /\ n$11 \notin decide_abort
        /\ vote_no' = vote_no \union {n$11}
        /\ abort_flag' = TRUE
        /\ decide_abort' = decide_abort \union {n$11}
        /\ (vote_yes' := vote_yes
          /\ alive' := alive
          /\ go_commit' := go_commit
          /\ go_abort' := go_abort
          /\ decide_commit' := decide_commit))
    \/ (\E n$12 \in Node:
      n$12 \in alive
        /\ alive' = alive \ {n$12}
        /\ abort_flag' = TRUE
        /\ (vote_yes' := vote_yes
          /\ vote_no' := vote_no
          /\ go_commit' := go_commit
          /\ go_abort' := go_abort
          /\ decide_commit' := decide_commit
          /\ decide_abort' := decide_abort))
    \/ ((\A n$15 \in Node: n$15 \notin go_commit)
      /\ (\A n$16 \in Node: n$16 \notin go_abort)
      /\ (\A n$17 \in Node: n$17 \in vote_yes)
      /\ go_commit' = Node
      /\ (vote_yes' := vote_yes
        /\ vote_no' := vote_no
        /\ alive' := alive
        /\ go_abort' := go_abort
        /\ decide_commit' := decide_commit
        /\ decide_abort' := decide_abort
        /\ abort_flag' := abort_flag))
    \/ ((\A n$18 \in Node: n$18 \notin go_commit)
      /\ (\A n$19 \in Node: n$19 \notin go_abort)
      /\ (\E n$20 \in Node: n$20 \in vote_no \/ n$20 \notin alive)
      /\ go_abort' = Node
      /\ (vote_yes' := vote_yes
        /\ vote_no' := vote_no
        /\ alive' := alive
        /\ go_commit' := go_commit
        /\ decide_commit' := decide_commit
        /\ decide_abort' := decide_abort
        /\ abort_flag' := abort_flag))
    \/ (\E n$13 \in Node:
      n$13 \in alive
        /\ n$13 \in go_commit
        /\ decide_commit' = decide_commit \union {n$13}
        /\ (vote_yes' := vote_yes
          /\ vote_no' := vote_no
          /\ alive' := alive
          /\ go_commit' := go_commit
          /\ go_abort' := go_abort
          /\ decide_abort' := decide_abort
          /\ abort_flag' := abort_flag))
    \/ (\E n$14 \in Node:
      n$14 \in alive
        /\ n$14 \in go_abort
        /\ decide_abort' = decide_abort \union {n$14}
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
    /\ ((\A n$21 \in Node:
        \A n2$4 \in Node: n$21 \in decide_commit => n2$4 \notin decide_abort)
      /\ (\A n$22 \in Node:
        \A n2$5 \in Node: n$22 \in decide_commit => n2$5 \in vote_yes)
      /\ (\A n$23 \in Node:
        \A n2$6 \in Node: n$23 \in decide_abort => abort_flag))

(*
  @type: (() => Bool);
*)
Inv ==
  ((TRUE
        /\ (vote_yes \in SUBSET Node
          /\ vote_no \in SUBSET Node
          /\ alive \in SUBSET Node
          /\ go_commit \in SUBSET Node
          /\ go_abort \in SUBSET Node
          /\ decide_commit \in SUBSET Node
          /\ decide_abort \in SUBSET Node
          /\ abort_flag \in BOOLEAN))
      /\ (\A x_0$3 \in Node: x_0$3 \in alive \/ ~(x_0$3 \in go_abort)))
    /\ (\A x_0$4 \in Node: x_0$4 \in alive \/ ~(x_0$4 \in decide_abort))

================================================================================
