------------------------ MODULE 09_OutPreprocessingPass ------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC, Apalache

CONSTANT
  (*
    @type: Set(RM);
  *)
  RM

VARIABLE
  (*
    @type: (RM -> Str);
  *)
  rmState

(*
  @type: (() => Bool);
*)
InitializeRM == RM = { "r1_OF_RM", "r2_OF_RM", "r3_OF_RM" }

(*
  @type: (() => Bool);
*)
P ==
  (DOMAIN rmState = RM
      /\ (\A t_1$1 \in RM:
        rmState[t_1$1] \in { "working", "prepared", "committed", "aborted" }))
    /\ (\A rm1$1 \in RM:
      \A rm2$1 \in RM:
        ~(rmState[rm1$1] = "aborted") \/ ~(rmState[rm2$1] = "committed"))

(*
  @type: (() => Bool);
*)
NOTP ==
  ~(DOMAIN rmState = RM
      /\ (\A t_2$1 \in RM:
        rmState[t_2$1] \in { "working", "prepared", "committed", "aborted" }))

(*
  @type: (() => Bool);
*)
Next ==
  \E rm$1 \in RM:
    (rmState[rm$1] = "working"
        /\ rmState' = [ rmState EXCEPT ![rm$1] = "prepared" ])
      \/ ((rmState[rm$1] = "prepared"
          /\ (\A rm$2 \in RM: rmState[rm$2] \in { "prepared", "committed" })
          /\ rmState' = [ rmState EXCEPT ![rm$1] = "committed" ])
        \/ (rmState[rm$1] \in { "working", "prepared" }
          /\ (\A rm$3 \in RM: ~(rmState[rm$3] = "committed"))
          /\ rmState' = [ rmState EXCEPT ![rm$1] = "aborted" ]))

InitializeRMPrimed == RM' = { "r1_OF_RM", "r2_OF_RM", "r3_OF_RM" }

PPrimed ==
  (\E t_3$1 \in [RM -> { "working", "prepared", "committed", "aborted" }]:
      rmState' = t_3$1)
    /\ (\A rm1$2 \in RM:
      \A rm2$2 \in RM:
        ~(rmState'[rm1$2] = "aborted") \/ ~(rmState'[rm2$2] = "committed"))

(*
  @type: Bool;
*)
VCInv_si_0 ==
  ~(DOMAIN rmState = RM
    /\ (\A t_4$1 \in RM:
      rmState[t_4$1] \in { "working", "prepared", "committed", "aborted" }))

(*
  @type: Bool;
*)
VCNotInv_si_0 ==
  DOMAIN rmState = RM
    /\ (\A t_5$1 \in RM:
      rmState[t_5$1] \in { "working", "prepared", "committed", "aborted" })

================================================================================