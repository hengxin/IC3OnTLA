------------------------------ MODULE 08_OutVCGen ------------------------------

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
InitializeNode == Node = { "n1_OF_NODE", "n2_OF_NODE", "n3_OF_NODE" }

(*
  @type: (() => Bool);
*)
Next ==
  (\E n$1 \in Node:
      lock_msg' = [ lock_msg EXCEPT ![n$1] = TRUE ]
        /\ (unlock_msg' := unlock_msg
          /\ grant_msg' := grant_msg
          /\ holds_lock' := holds_lock
          /\ server_holds_lock' := server_holds_lock))
    \/ (\E n$2 \in Node:
      server_holds_lock
        /\ lock_msg[n$2]
        /\ server_holds_lock' = FALSE
        /\ lock_msg' = [ k$1 \in Node |-> lock_msg[k$1] /\ k$1 /= n$2 ]
        /\ grant_msg' = [ grant_msg EXCEPT ![n$2] = TRUE ]
        /\ (unlock_msg' := unlock_msg /\ holds_lock' := holds_lock))
    \/ (\E n$3 \in Node:
      grant_msg[n$3]
        /\ grant_msg' = [ k$2 \in Node |-> grant_msg[k$2] /\ k$2 /= n$3 ]
        /\ holds_lock' = [ holds_lock EXCEPT ![n$3] = TRUE ]
        /\ (lock_msg' := lock_msg
          /\ unlock_msg' := unlock_msg
          /\ server_holds_lock' := server_holds_lock))
    \/ (\E n$4 \in Node:
      holds_lock[n$4]
        /\ holds_lock' = [ k$3 \in Node |-> holds_lock[k$3] /\ k$3 /= n$4 ]
        /\ unlock_msg' = [ unlock_msg EXCEPT ![n$4] = TRUE ]
        /\ (lock_msg' := lock_msg
          /\ grant_msg' := grant_msg
          /\ server_holds_lock' := server_holds_lock))
    \/ (\E n$5 \in Node:
      unlock_msg[n$5]
        /\ unlock_msg' = [ k$4 \in Node |-> unlock_msg[k$4] /\ k$4 /= n$5 ]
        /\ server_holds_lock' = TRUE
        /\ (lock_msg' := lock_msg
          /\ grant_msg' := grant_msg
          /\ holds_lock' := holds_lock))

(*
  @type: (() => Bool);
*)
P ==
  (\A x$1 \in Node:
      \A y$1 \in Node: holds_lock[x$1] /\ holds_lock[y$1] => x$1 = y$1)
    /\ (lock_msg \in [Node -> BOOLEAN]
      /\ grant_msg \in [Node -> BOOLEAN]
      /\ unlock_msg \in [Node -> BOOLEAN]
      /\ holds_lock \in [Node -> BOOLEAN]
      /\ server_holds_lock \in BOOLEAN)

InitializeNodePrimed == Node' = { "n1_OF_NODE", "n2_OF_NODE", "n3_OF_NODE" }

PPrimed ==
  (\A x$1 \in Node:
      \A y$1 \in Node: holds_lock'[x$1] /\ holds_lock'[y$1] => x$1 = y$1)
    /\ (lock_msg' \in [Node -> BOOLEAN]
      /\ grant_msg' \in [Node -> BOOLEAN]
      /\ unlock_msg' \in [Node -> BOOLEAN]
      /\ holds_lock' \in [Node -> BOOLEAN]
      /\ server_holds_lock' \in BOOLEAN)

(*
  @type: Bool;
*)
VCInv_si_0 ==
  \A x$1 \in Node:
    \A y$1 \in Node: holds_lock[x$1] /\ holds_lock[y$1] => x$1 = y$1

(*
  @type: Bool;
*)
VCNotInv_si_0 ==
  ~(\A x$1 \in Node:
    \A y$1 \in Node: holds_lock[x$1] /\ holds_lock[y$1] => x$1 = y$1)

(*
  @type: Bool;
*)
VCInv_si_1 == lock_msg \in [Node -> BOOLEAN]

(*
  @type: Bool;
*)
VCNotInv_si_1 == ~(lock_msg \in [Node -> BOOLEAN])

(*
  @type: Bool;
*)
VCInv_si_2 == grant_msg \in [Node -> BOOLEAN]

(*
  @type: Bool;
*)
VCNotInv_si_2 == ~(grant_msg \in [Node -> BOOLEAN])

(*
  @type: Bool;
*)
VCInv_si_3 == unlock_msg \in [Node -> BOOLEAN]

(*
  @type: Bool;
*)
VCNotInv_si_3 == ~(unlock_msg \in [Node -> BOOLEAN])

(*
  @type: Bool;
*)
VCInv_si_4 == holds_lock \in [Node -> BOOLEAN]

(*
  @type: Bool;
*)
VCNotInv_si_4 == ~(holds_lock \in [Node -> BOOLEAN])

(*
  @type: Bool;
*)
VCInv_si_5 == server_holds_lock \in BOOLEAN

(*
  @type: Bool;
*)
VCNotInv_si_5 == ~(server_holds_lock \in BOOLEAN)

================================================================================
