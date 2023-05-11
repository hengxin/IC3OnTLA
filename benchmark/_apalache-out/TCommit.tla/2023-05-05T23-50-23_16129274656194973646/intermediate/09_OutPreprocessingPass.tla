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
Init == rmState = [ rm$1 \in RM |-> "working" ]

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
Next ==
  \E rm$2 \in RM:
    (rmState[rm$2] = "working"
        /\ rmState' = [ rmState EXCEPT ![rm$2] = "prepared" ])
      \/ ((rmState[rm$2] = "prepared"
          /\ (\A rm$3 \in RM: rmState[rm$3] \in { "prepared", "committed" })
          /\ rmState' = [ rmState EXCEPT ![rm$2] = "committed" ])
        \/ (rmState[rm$2] \in { "working", "prepared" }
          /\ (\A rm$4 \in RM: ~(rmState[rm$4] = "committed"))
          /\ rmState' = [ rmState EXCEPT ![rm$2] = "aborted" ]))

InitializeRMPrimed == RM' = { "r1_OF_RM", "r2_OF_RM", "r3_OF_RM" }

InitPrimed == rmState' = [ rm$5 \in RM |-> "working" ]

(*
  @type: Bool;
*)
VCInv_si_0 ==
  DOMAIN rmState = RM
    /\ (\A t_2$1 \in RM:
      rmState[t_2$1] \in { "working", "prepared", "committed", "aborted" })

(*
  @type: Bool;
*)
VCNotInv_si_0 ==
  ~(DOMAIN rmState = RM
    /\ (\A t_3$1 \in RM:
      rmState[t_3$1] \in { "working", "prepared", "committed", "aborted" }))

(*
  @type: Bool;
*)
VCInv_si_1 ==
  \A rm1$2 \in RM:
    \A rm2$2 \in RM:
      ~(rmState[rm1$2] = "aborted") \/ ~(rmState[rm2$2] = "committed")

(*
  @type: Bool;
*)
VCNotInv_si_1 ==
  \E rm1$3 \in RM:
    \E rm2$3 \in RM: rmState[rm1$3] = "aborted" /\ rmState[rm2$3] = "committed"

================================================================================
