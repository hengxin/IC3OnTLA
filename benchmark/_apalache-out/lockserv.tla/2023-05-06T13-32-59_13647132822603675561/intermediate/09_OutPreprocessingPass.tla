------------------------ MODULE 09_OutPreprocessingPass ------------------------

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
        /\ lock_msg' = [ k$1 \in Node |-> lock_msg[k$1] /\ ~(k$1 = n$6) ]
        /\ grant_msg' = [ grant_msg EXCEPT ![n$6] = TRUE ]
        /\ (unlock_msg' := unlock_msg /\ holds_lock' := holds_lock))
    \/ (\E n$7 \in Node:
      grant_msg[n$7]
        /\ grant_msg' = [ k$2 \in Node |-> grant_msg[k$2] /\ ~(k$2 = n$7) ]
        /\ holds_lock' = [ holds_lock EXCEPT ![n$7] = TRUE ]
        /\ (lock_msg' := lock_msg
          /\ unlock_msg' := unlock_msg
          /\ server_holds_lock' := server_holds_lock))
    \/ (\E n$8 \in Node:
      holds_lock[n$8]
        /\ holds_lock' = [ k$3 \in Node |-> holds_lock[k$3] /\ ~(k$3 = n$8) ]
        /\ unlock_msg' = [ unlock_msg EXCEPT ![n$8] = TRUE ]
        /\ (lock_msg' := lock_msg
          /\ grant_msg' := grant_msg
          /\ server_holds_lock' := server_holds_lock))
    \/ (\E n$9 \in Node:
      unlock_msg[n$9]
        /\ unlock_msg' = [ k$4 \in Node |-> unlock_msg[k$4] /\ ~(k$4 = n$9) ]
        /\ server_holds_lock' = TRUE
        /\ (lock_msg' := lock_msg
          /\ grant_msg' := grant_msg
          /\ holds_lock' := holds_lock))

(*
  @type: (() => Bool);
*)
P ==
  (\A x$1 \in Node:
      \A y$1 \in Node: (~(holds_lock[x$1]) \/ ~(holds_lock[y$1])) \/ x$1 = y$1)
    /\ ((DOMAIN lock_msg = Node
        /\ (\A t_1$1 \in Node: lock_msg[t_1$1] \in BOOLEAN))
      /\ (DOMAIN grant_msg = Node
        /\ (\A t_2$1 \in Node: grant_msg[t_2$1] \in BOOLEAN))
      /\ (DOMAIN unlock_msg = Node
        /\ (\A t_3$1 \in Node: unlock_msg[t_3$1] \in BOOLEAN))
      /\ (DOMAIN holds_lock = Node
        /\ (\A t_4$1 \in Node: holds_lock[t_4$1] \in BOOLEAN))
      /\ server_holds_lock \in BOOLEAN)

InitializeNodePrimed == Node' = { "n1_OF_NODE", "n2_OF_NODE", "n3_OF_NODE" }

InitPrimed ==
  lock_msg' = [ n$10 \in Node |-> FALSE ]
    /\ unlock_msg' = [ n$11 \in Node |-> FALSE ]
    /\ grant_msg' = [ n$12 \in Node |-> FALSE ]
    /\ holds_lock' = [ n$13 \in Node |-> FALSE ]
    /\ server_holds_lock' = TRUE

(*
  @type: Bool;
*)
VCInv_si_0 ==
  \A x$2 \in Node:
    \A y$2 \in Node: (~(holds_lock[x$2]) \/ ~(holds_lock[y$2])) \/ x$2 = y$2

(*
  @type: Bool;
*)
VCNotInv_si_0 ==
  \E x$3 \in Node:
    \E y$3 \in Node: (holds_lock[x$3] /\ holds_lock[y$3]) /\ ~(x$3 = y$3)

(*
  @type: Bool;
*)
VCInv_si_1 ==
  DOMAIN lock_msg = Node /\ (\A t_5$1 \in Node: lock_msg[t_5$1] \in BOOLEAN)

(*
  @type: Bool;
*)
VCNotInv_si_1 ==
  ~(DOMAIN lock_msg = Node /\ (\A t_6$1 \in Node: lock_msg[t_6$1] \in BOOLEAN))

(*
  @type: Bool;
*)
VCInv_si_2 ==
  DOMAIN grant_msg = Node /\ (\A t_7$1 \in Node: grant_msg[t_7$1] \in BOOLEAN)

(*
  @type: Bool;
*)
VCNotInv_si_2 ==
  ~(DOMAIN grant_msg = Node /\ (\A t_8$1 \in Node: grant_msg[t_8$1] \in BOOLEAN))

(*
  @type: Bool;
*)
VCInv_si_3 ==
  DOMAIN unlock_msg = Node /\ (\A t_9$1 \in Node: unlock_msg[t_9$1] \in BOOLEAN)

(*
  @type: Bool;
*)
VCNotInv_si_3 ==
  ~(DOMAIN unlock_msg = Node
    /\ (\A t_a$1 \in Node: unlock_msg[t_a$1] \in BOOLEAN))

(*
  @type: Bool;
*)
VCInv_si_4 ==
  DOMAIN holds_lock = Node /\ (\A t_b$1 \in Node: holds_lock[t_b$1] \in BOOLEAN)

(*
  @type: Bool;
*)
VCNotInv_si_4 ==
  ~(DOMAIN holds_lock = Node
    /\ (\A t_c$1 \in Node: holds_lock[t_c$1] \in BOOLEAN))

(*
  @type: Bool;
*)
VCInv_si_5 == server_holds_lock \in BOOLEAN

(*
  @type: Bool;
*)
VCNotInv_si_5 == ~(server_holds_lock \in BOOLEAN)

================================================================================
