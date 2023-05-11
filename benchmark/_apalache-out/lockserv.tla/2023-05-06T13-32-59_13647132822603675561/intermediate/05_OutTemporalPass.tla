-------------------------- MODULE 05_OutTemporalPass --------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC, Apalache

CONSTANT
  (*
    @type: Set(NODE);
  *)
  Node

VARIABLE
  (*
    @type: (NODE -> Bool);
  *)
  lock_msg

VARIABLE
  (*
    @type: Bool;
  *)
  server_holds_lock

VARIABLE
  (*
    @type: (NODE -> Bool);
  *)
  holds_lock

VARIABLE
  (*
    @type: (NODE -> Bool);
  *)
  grant_msg

VARIABLE
  (*
    @type: (NODE -> Bool);
  *)
  unlock_msg

(*
  @type: (() => Bool);
*)
Init ==
  lock_msg = [ n$1 \in Node |-> FALSE ]
    /\ unlock_msg = [ n$2 \in Node |-> FALSE ]
    /\ grant_msg = [ n$3 \in Node |-> FALSE ]
    /\ holds_lock = [ n$4 \in Node |-> FALSE ]
    /\ server_holds_lock = TRUE

(*
  @type: (() => Bool);
*)
InitializeNode == Node = { "n1_OF_NODE", "n2_OF_NODE", "n3_OF_NODE" }

(*
  @type: (() => Bool);
*)
Next ==
  (\E n$5 \in Node:
      lock_msg' = [ lock_msg EXCEPT ![n$5] = TRUE ]
        /\ (unlock_msg' := unlock_msg
          /\ grant_msg' := grant_msg
          /\ holds_lock' := holds_lock
          /\ server_holds_lock' := server_holds_lock))
    \/ (\E n$6 \in Node:
      server_holds_lock
        /\ lock_msg[n$6]
        /\ server_holds_lock' = FALSE
        /\ lock_msg' = [ k$5 \in Node |-> lock_msg[k$5] /\ k$5 /= n$6 ]
        /\ grant_msg' = [ grant_msg EXCEPT ![n$6] = TRUE ]
        /\ (unlock_msg' := unlock_msg /\ holds_lock' := holds_lock))
    \/ (\E n$7 \in Node:
      grant_msg[n$7]
        /\ grant_msg' = [ k$6 \in Node |-> grant_msg[k$6] /\ k$6 /= n$7 ]
        /\ holds_lock' = [ holds_lock EXCEPT ![n$7] = TRUE ]
        /\ (lock_msg' := lock_msg
          /\ unlock_msg' := unlock_msg
          /\ server_holds_lock' := server_holds_lock))
    \/ (\E n$8 \in Node:
      holds_lock[n$8]
        /\ holds_lock' = [ k$7 \in Node |-> holds_lock[k$7] /\ k$7 /= n$8 ]
        /\ unlock_msg' = [ unlock_msg EXCEPT ![n$8] = TRUE ]
        /\ (lock_msg' := lock_msg
          /\ grant_msg' := grant_msg
          /\ server_holds_lock' := server_holds_lock))
    \/ (\E n$9 \in Node:
      unlock_msg[n$9]
        /\ unlock_msg' = [ k$8 \in Node |-> unlock_msg[k$8] /\ k$8 /= n$9 ]
        /\ server_holds_lock' = TRUE
        /\ (lock_msg' := lock_msg
          /\ grant_msg' := grant_msg
          /\ holds_lock' := holds_lock))

(*
  @type: (() => Bool);
*)
P ==
  (\A x$2 \in Node:
      \A y$2 \in Node: holds_lock[x$2] /\ holds_lock[y$2] => x$2 = y$2)
    /\ (lock_msg \in [Node -> BOOLEAN]
      /\ grant_msg \in [Node -> BOOLEAN]
      /\ unlock_msg \in [Node -> BOOLEAN]
      /\ holds_lock \in [Node -> BOOLEAN]
      /\ server_holds_lock \in BOOLEAN)

================================================================================
