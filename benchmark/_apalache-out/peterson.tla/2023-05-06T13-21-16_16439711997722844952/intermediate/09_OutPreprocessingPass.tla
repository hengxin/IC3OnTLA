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
InitializeProcSet == ProcSet = { "p0_OF_PROCSET", "p1_OF_PROCSET" }

(*
  @type: (() => Bool);
*)
ASSUME(Cardinality(ProcSet) = 2)

(*
  @type: (() => Bool);
*)
Next ==
  \E self$1 \in ProcSet:
    \E other$1 \in ProcSet:
      (pc[self$1] = "a1"
          /\ TRUE
          /\ pc' = [ pc EXCEPT ![self$1] = "a2" ]
          /\ (flag' := flag /\ turn' := turn))
        \/ (pc[self$1] = "a2"
          /\ flag' = [ flag EXCEPT ![self$1] = TRUE ]
          /\ pc' = [ pc EXCEPT ![self$1] = "a3" ]
          /\ turn' = turn)
        \/ (((((pc[self$1] = "a3") /\ ~(self$1 = other$1)) /\ turn' = other$1)
            /\ pc' = [ pc EXCEPT ![self$1] = "a4" ])
          /\ flag' = flag)
        \/ (~(self$1 = other$1)
          /\ pc[self$1] = "a4"
          /\ (flag[other$1] = FALSE \/ turn = self$1)
          /\ pc' = [ pc EXCEPT ![self$1] = "cs" ]
          /\ (flag' := flag /\ turn' := turn))
        \/ (pc[self$1] = "cs"
          /\ TRUE
          /\ pc' = [ pc EXCEPT ![self$1] = "a5" ]
          /\ (flag' := flag /\ turn' := turn))
        \/ (pc[self$1] = "a5"
          /\ flag' = [ flag EXCEPT ![self$1] = FALSE ]
          /\ pc' = [ pc EXCEPT ![self$1] = "a1" ]
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

PPrimed ==
  ((\E t_3$1 \in [ProcSet -> BOOLEAN]: flag' = t_3$1)
      /\ (\E t_4$1 \in ProcSet: turn' = t_4$1)
      /\ (\E t_5$1 \in [ProcSet -> { "a1", "a2", "a3", "a4", "a5", "cs" }]:
        pc' = t_5$1))
    /\ (\A p$2 \in ProcSet:
      \A q$2 \in ProcSet:
        p$2 = q$2 \/ (~(pc'[p$2] = "cs") \/ ~(pc'[q$2] = "cs")))

(*
  @type: Bool;
*)
VCInv_si_0 ==
  DOMAIN flag = ProcSet /\ (\A t_6$1 \in ProcSet: flag[t_6$1] \in BOOLEAN)

(*
  @type: Bool;
*)
VCNotInv_si_0 ==
  ~(DOMAIN flag = ProcSet /\ (\A t_7$1 \in ProcSet: flag[t_7$1] \in BOOLEAN))

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
    /\ (\A t_8$1 \in ProcSet:
      pc[t_8$1] \in { "a1", "a2", "a3", "a4", "a5", "cs" })

(*
  @type: Bool;
*)
VCNotInv_si_2 ==
  ~(DOMAIN pc = ProcSet
    /\ (\A t_9$1 \in ProcSet:
      pc[t_9$1] \in { "a1", "a2", "a3", "a4", "a5", "cs" }))

(*
  @type: Bool;
*)
VCInv_si_3 ==
  \A p$3 \in ProcSet:
    \A q$3 \in ProcSet: p$3 = q$3 \/ (~(pc[p$3] = "cs") \/ ~(pc[q$3] = "cs"))

(*
  @type: Bool;
*)
VCNotInv_si_3 ==
  \E p$4 \in ProcSet:
    \E q$4 \in ProcSet: ~(p$4 = q$4) /\ (pc[p$4] = "cs" /\ pc[q$4] = "cs")

================================================================================
