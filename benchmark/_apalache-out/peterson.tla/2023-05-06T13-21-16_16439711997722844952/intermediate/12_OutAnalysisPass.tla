-------------------------- MODULE 12_OutAnalysisPass --------------------------

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
ASSUME(Cardinality(ProcSet) = 2)

(*
  @type: (() => Bool);
*)
CInit_si_0 == ProcSet' := { "p0_OF_PROCSET", "p1_OF_PROCSET" }

(*
  @type: (() => Bool);
*)
Init_si_0000 ==
  (Skolem((\E t_3$1 \in [ProcSet -> BOOLEAN]: flag' := t_3$1))
      /\ Skolem((\E t_4$1 \in ProcSet: turn' := t_4$1))
      /\ Skolem((\E t_5$1 \in [ProcSet
        -> { "a1", "a2", "a3", "a4", "a5", "cs" }]:
        pc' := t_5$1)))
    /\ (\A p$1 \in ProcSet:
      \A q$1 \in ProcSet:
        p$1 = q$1 \/ (~(pc'[p$1] = "cs") \/ ~(pc'[q$1] = "cs")))

(*
  @type: (() => Bool);
*)
Next_si_0000 ==
  Skolem((\E self$1 \in ProcSet:
    Skolem((\E other$1 \in ProcSet:
      pc[self$1] = "a2"
        /\ flag' := [ flag EXCEPT ![self$1] = TRUE ]
        /\ pc' := [ pc EXCEPT ![self$1] = "a3" ]
        /\ turn' := turn))))

(*
  @type: (() => Bool);
*)
Next_si_0001 ==
  Skolem((\E self$2 \in ProcSet:
    Skolem((\E other$2 \in ProcSet:
      pc[self$2] = "a1"
        /\ pc' := [ pc EXCEPT ![self$2] = "a2" ]
        /\ (flag' := flag /\ turn' := turn)))))

(*
  @type: (() => Bool);
*)
Next_si_0002 ==
  Skolem((\E self$3 \in ProcSet:
    Skolem((\E other$3 \in ProcSet:
      pc[self$3] = "a5"
        /\ flag' := [ flag EXCEPT ![self$3] = FALSE ]
        /\ pc' := [ pc EXCEPT ![self$3] = "a1" ]
        /\ turn' := turn))))

(*
  @type: (() => Bool);
*)
Next_si_0003 ==
  Skolem((\E self$4 \in ProcSet:
    Skolem((\E other$4 \in ProcSet:
      (((pc[self$4] = "a3" /\ ~(self$4 = other$4)) /\ turn' := other$4)
          /\ pc' := [ pc EXCEPT ![self$4] = "a4" ])
        /\ flag' := flag))))

(*
  @type: (() => Bool);
*)
Next_si_0004 ==
  Skolem((\E self$5 \in ProcSet:
    Skolem((\E other$5 \in ProcSet:
      ~(self$5 = other$5)
        /\ pc[self$5] = "a4"
        /\ (flag[other$5] = FALSE \/ turn = self$5)
        /\ pc' := [ pc EXCEPT ![self$5] = "cs" ]
        /\ (flag' := flag /\ turn' := turn)))))

(*
  @type: (() => Bool);
*)
Next_si_0005 ==
  Skolem((\E self$6 \in ProcSet:
    Skolem((\E other$6 \in ProcSet:
      pc[self$6] = "cs"
        /\ pc' := [ pc EXCEPT ![self$6] = "a5" ]
        /\ (flag' := flag /\ turn' := turn)))))

(*
  @type: Bool;
*)
VCInv_si_0 == DOMAIN flag = ProcSet

(*
  @type: Bool;
*)
VCNotInv_si_0 == ~(DOMAIN flag = ProcSet)

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
  \A p$2 \in ProcSet:
    \A q$2 \in ProcSet: p$2 = q$2 \/ (~(pc[p$2] = "cs") \/ ~(pc[q$2] = "cs"))

(*
  @type: Bool;
*)
VCNotInv_si_3 ==
  Skolem((\E p$3 \in ProcSet:
    Skolem((\E q$3 \in ProcSet:
      ~(p$3 = q$3) /\ (pc[p$3] = "cs" /\ pc[q$3] = "cs")))))

================================================================================
