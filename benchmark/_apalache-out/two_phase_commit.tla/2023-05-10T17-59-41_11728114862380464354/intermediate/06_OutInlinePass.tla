--------------------------- MODULE 06_OutInlinePass ---------------------------

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
  (\E n$1 \in Node:
      n$1 \in alive
        /\ n$1 \notin vote_no
        /\ n$1 \notin decide_commit
        /\ n$1 \notin decide_abort
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
        /\ n$2 \notin vote_yes
        /\ n$2 \notin decide_commit
        /\ n$2 \notin decide_abort
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
        /\ alive' = alive \ {n$3}
        /\ abort_flag' = TRUE
        /\ (vote_yes' := vote_yes
          /\ vote_no' := vote_no
          /\ go_commit' := go_commit
          /\ go_abort' := go_abort
          /\ decide_commit' := decide_commit
          /\ decide_abort' := decide_abort))
    \/ ((\A n$4 \in Node: n$4 \notin go_commit)
      /\ (\A n$5 \in Node: n$5 \notin go_abort)
      /\ (\A n$6 \in Node: n$6 \in vote_yes)
      /\ go_commit' = Node
      /\ (vote_yes' := vote_yes
        /\ vote_no' := vote_no
        /\ alive' := alive
        /\ go_abort' := go_abort
        /\ decide_commit' := decide_commit
        /\ decide_abort' := decide_abort
        /\ abort_flag' := abort_flag))
    \/ ((\A n$7 \in Node: n$7 \notin go_commit)
      /\ (\A n$8 \in Node: n$8 \notin go_abort)
      /\ (\E n$9 \in Node: n$9 \in vote_no \/ n$9 \notin alive)
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
        \A n2$1 \in Node: n$12 \in decide_commit => n2$1 \notin decide_abort)
      /\ (\A n$13 \in Node:
        \A n2$2 \in Node: n$13 \in decide_commit => n2$2 \in vote_yes)
      /\ (\A n$14 \in Node:
        \A n2$3 \in Node: n$14 \in decide_abort => abort_flag))

(*
  @type: (() => Bool);
*)
Inv ==
  ((((TRUE
            /\ (vote_yes \in SUBSET Node
              /\ vote_no \in SUBSET Node
              /\ alive \in SUBSET Node
              /\ go_commit \in SUBSET Node
              /\ go_abort \in SUBSET Node
              /\ decide_commit \in SUBSET Node
              /\ decide_abort \in SUBSET Node
              /\ abort_flag \in BOOLEAN))
          /\ (\A x_0$1 \in Node: x_0$1 \in alive \/ ~(x_0$1 \in go_abort)))
        /\ (\A x_0$2 \in Node: x_0$2 \in alive \/ ~(x_0$2 \in decide_abort)))
      /\ (\A x_0$3 \in Node: x_0$3 \in go_commit \/ ~(x_0$3 \in decide_commit)))
    /\ (\A x_0$4 \in Node: x_0$4 \in vote_yes \/ ~(x_0$4 \in vote_no))

================================================================================
