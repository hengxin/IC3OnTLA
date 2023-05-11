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
        /\ lock_msg' = [ k$1 \in Node |-> lock_msg[k$1] /\ ~(k$1 = n$2) ]
        /\ grant_msg' = [ grant_msg EXCEPT ![n$2] = TRUE ]
        /\ (unlock_msg' := unlock_msg /\ holds_lock' := holds_lock))
    \/ (\E n$3 \in Node:
      grant_msg[n$3]
        /\ grant_msg' = [ k$2 \in Node |-> grant_msg[k$2] /\ ~(k$2 = n$3) ]
        /\ holds_lock' = [ holds_lock EXCEPT ![n$3] = TRUE ]
        /\ (lock_msg' := lock_msg
          /\ unlock_msg' := unlock_msg
          /\ server_holds_lock' := server_holds_lock))
    \/ (\E n$4 \in Node:
      holds_lock[n$4]
        /\ holds_lock' = [ k$3 \in Node |-> holds_lock[k$3] /\ ~(k$3 = n$4) ]
        /\ unlock_msg' = [ unlock_msg EXCEPT ![n$4] = TRUE ]
        /\ (lock_msg' := lock_msg
          /\ grant_msg' := grant_msg
          /\ server_holds_lock' := server_holds_lock))
    \/ (\E n$5 \in Node:
      unlock_msg[n$5]
        /\ unlock_msg' = [ k$4 \in Node |-> unlock_msg[k$4] /\ ~(k$4 = n$5) ]
        /\ server_holds_lock' = TRUE
        /\ (lock_msg' := lock_msg
          /\ grant_msg' := grant_msg
          /\ holds_lock' := holds_lock))

(*
  @type: (() => Bool);
*)
P ==
  ((DOMAIN lock_msg = Node /\ (\A t_1$1 \in Node: lock_msg[t_1$1] \in BOOLEAN))
      /\ (DOMAIN grant_msg = Node
        /\ (\A t_2$1 \in Node: grant_msg[t_2$1] \in BOOLEAN))
      /\ (DOMAIN unlock_msg = Node
        /\ (\A t_3$1 \in Node: unlock_msg[t_3$1] \in BOOLEAN))
      /\ (DOMAIN holds_lock = Node
        /\ (\A t_4$1 \in Node: holds_lock[t_4$1] \in BOOLEAN))
      /\ server_holds_lock \in BOOLEAN)
    /\ (\A x$1 \in Node:
      \A y$1 \in Node: (~(holds_lock[x$1]) \/ ~(holds_lock[y$1])) \/ x$1 = y$1)

InitializeNodePrimed == Node' = { "n1_OF_NODE", "n2_OF_NODE", "n3_OF_NODE" }

PPrimed ==
  ((\E t_5$1 \in [Node -> BOOLEAN]: lock_msg' = t_5$1)
      /\ (\E t_6$1 \in [Node -> BOOLEAN]: grant_msg' = t_6$1)
      /\ (\E t_7$1 \in [Node -> BOOLEAN]: unlock_msg' = t_7$1)
      /\ (\E t_8$1 \in [Node -> BOOLEAN]: holds_lock' = t_8$1)
      /\ (\E t_9$1 \in BOOLEAN: server_holds_lock' = t_9$1))
    /\ (\A x$2 \in Node:
      \A y$2 \in Node: (~(holds_lock'[x$2]) \/ ~(holds_lock'[y$2])) \/ x$2 = y$2)

(*
  @type: Bool;
*)
VCInv_si_0 ==
  DOMAIN lock_msg = Node /\ (\A t_a$1 \in Node: lock_msg[t_a$1] \in BOOLEAN)

(*
  @type: Bool;
*)
VCNotInv_si_0 ==
  ~(DOMAIN lock_msg = Node /\ (\A t_b$1 \in Node: lock_msg[t_b$1] \in BOOLEAN))

(*
  @type: Bool;
*)
VCInv_si_1 ==
  DOMAIN grant_msg = Node /\ (\A t_c$1 \in Node: grant_msg[t_c$1] \in BOOLEAN)

(*
  @type: Bool;
*)
VCNotInv_si_1 ==
  ~(DOMAIN grant_msg = Node /\ (\A t_d$1 \in Node: grant_msg[t_d$1] \in BOOLEAN))

(*
  @type: Bool;
*)
VCInv_si_2 ==
  DOMAIN unlock_msg = Node /\ (\A t_e$1 \in Node: unlock_msg[t_e$1] \in BOOLEAN)

(*
  @type: Bool;
*)
VCNotInv_si_2 ==
  ~(DOMAIN unlock_msg = Node
    /\ (\A t_f$1 \in Node: unlock_msg[t_f$1] \in BOOLEAN))

(*
  @type: Bool;
*)
VCInv_si_3 ==
  DOMAIN holds_lock = Node /\ (\A t_g$1 \in Node: holds_lock[t_g$1] \in BOOLEAN)

(*
  @type: Bool;
*)
VCNotInv_si_3 ==
  ~(DOMAIN holds_lock = Node
    /\ (\A t_h$1 \in Node: holds_lock[t_h$1] \in BOOLEAN))

(*
  @type: Bool;
*)
VCInv_si_4 == server_holds_lock \in BOOLEAN

(*
  @type: Bool;
*)
VCNotInv_si_4 == ~(server_holds_lock \in BOOLEAN)

(*
  @type: Bool;
*)
VCInv_si_5 ==
  \A x$3 \in Node:
    \A y$3 \in Node: (~(holds_lock[x$3]) \/ ~(holds_lock[y$3])) \/ x$3 = y$3

(*
  @type: Bool;
*)
VCNotInv_si_5 ==
  \E x$4 \in Node:
    \E y$4 \in Node: (holds_lock[x$4] /\ holds_lock[y$4]) /\ ~(x$4 = y$4)

================================================================================
