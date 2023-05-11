------------------------ MODULE 09_OutPreprocessingPass ------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC, Apalache

CONSTANT
  (*
    @type: Set(PROCSET);
  *)
  ProcSet

VARIABLE
  (*
    @type: (PROCSET -> Bool);
  *)
  flag

VARIABLE
  (*
    @type: (PROCSET -> Str);
  *)
  pc

VARIABLE
  (*
    @type: PROCSET;
  *)
  turn

(*
  @type: (() => Bool);
*)
Init ==
  flag = [ proc$1 \in ProcSet |-> FALSE ]
    /\ turn \in ProcSet
    /\ pc = [ self$1 \in ProcSet |-> "a1" ]

(*
  @type: (() => Bool);
*)
InitializeProcSet == ProcSet = { "p0_OF_PROCSET", "p1_OF_PROCSET" }

(*
  @type: (() => Bool);
*)
ASSUME(Cardinality(ProcSet) = 2)

(*
  @type: (() => Bool);
*)
Next ==
  \E self$2 \in ProcSet:
    \E other$1 \in ProcSet:
      (pc[self$2] = "a1"
          /\ TRUE
          /\ pc' = [ pc EXCEPT ![self$2] = "a2" ]
          /\ (flag' := flag /\ turn' := turn))
        \/ (pc[self$2] = "a2"
          /\ flag' = [ flag EXCEPT ![self$2] = TRUE ]
          /\ pc' = [ pc EXCEPT ![self$2] = "a3" ]
          /\ turn' = turn)
        \/ (((((pc[self$2] = "a3") /\ ~(self$2 = other$1)) /\ turn' = other$1)
            /\ pc' = [ pc EXCEPT ![self$2] = "a4" ])
          /\ flag' = flag)
        \/ (~(self$2 = other$1)
          /\ pc[self$2] = "a4"
          /\ (flag[other$1] = FALSE \/ turn = self$2)
          /\ pc' = [ pc EXCEPT ![self$2] = "cs" ]
          /\ (flag' := flag /\ turn' := turn))
        \/ (pc[self$2] = "cs"
          /\ TRUE
          /\ pc' = [ pc EXCEPT ![self$2] = "a5" ]
          /\ (flag' := flag /\ turn' := turn))
        \/ (pc[self$2] = "a5"
          /\ flag' = [ flag EXCEPT ![self$2] = FALSE ]
          /\ pc' = [ pc EXCEPT ![self$2] = "a1" ]
          /\ turn' = turn)

(*
  @type: (() => Bool);
*)
P ==
  ((DOMAIN flag = ProcSet /\ (\A t_1$1 \in ProcSet: flag[t_1$1] \in BOOLEAN))
      /\ turn \in ProcSet
      /\ (DOMAIN pc = ProcSet
        /\ (\A t_2$1 \in ProcSet:
          pc[t_2$1] \in { "a1", "a2", "a3", "a4", "a5", "cs" })))
    /\ (\A p$1 \in ProcSet:
      \A q$1 \in ProcSet: p$1 = q$1 \/ (~(pc[p$1] = "cs") \/ ~(pc[q$1] = "cs")))

InitializeProcSetPrimed == ProcSet' = { "p0_OF_PROCSET", "p1_OF_PROCSET" }

InitPrimed ==
  flag' = [ proc$2 \in ProcSet |-> FALSE ]
    /\ (\E t_3$1 \in ProcSet: turn' = t_3$1)
    /\ pc' = [ self$3 \in ProcSet |-> "a1" ]

(*
  @type: Bool;
*)
VCInv_si_0 ==
  DOMAIN flag = ProcSet /\ (\A t_4$1 \in ProcSet: flag[t_4$1] \in BOOLEAN)

(*
  @type: Bool;
*)
VCNotInv_si_0 ==
  ~(DOMAIN flag = ProcSet /\ (\A t_5$1 \in ProcSet: flag[t_5$1] \in BOOLEAN))

(*
  @type: Bool;
*)
VCInv_si_1 == turn \in ProcSet

(*
  @type: Bool;
*)
VCNotInv_si_1 == ~(turn \in ProcSet)

(*
  @type: Bool;
*)
VCInv_si_2 ==
  DOMAIN pc = ProcSet
    /\ (\A t_6$1 \in ProcSet:
      pc[t_6$1] \in { "a1", "a2", "a3", "a4", "a5", "cs" })

(*
  @type: Bool;
*)
VCNotInv_si_2 ==
  ~(DOMAIN pc = ProcSet
    /\ (\A t_7$1 \in ProcSet:
      pc[t_7$1] \in { "a1", "a2", "a3", "a4", "a5", "cs" }))

(*
  @type: Bool;
*)
VCInv_si_3 ==
  \A p$2 \in ProcSet:
    \A q$2 \in ProcSet: p$2 = q$2 \/ (~(pc[p$2] = "cs") \/ ~(pc[q$2] = "cs"))

(*
  @type: Bool;
*)
VCNotInv_si_3 ==
  \E p$3 \in ProcSet:
    \E q$3 \in ProcSet: ~(p$3 = q$3) /\ (pc[p$3] = "cs" /\ pc[q$3] = "cs")

================================================================================
