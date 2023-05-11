--------------------------- MODULE 06_OutInlinePass ---------------------------

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
        \/ (((((pc[self$2] = "a3") /\ self$2 /= other$1) /\ turn' = other$1)
            /\ pc' = [ pc EXCEPT ![self$2] = "a4" ])
          /\ flag' = flag)
        \/ (self$2 /= other$1
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
  (flag \in [ProcSet -> BOOLEAN]
      /\ turn \in ProcSet
      /\ pc \in [ProcSet -> { "a1", "a2", "a3", "a4", "a5", "cs" }])
    /\ (\A p$1 \in ProcSet:
      \A q$1 \in ProcSet: p$1 /= q$1 => ~(pc[p$1] = "cs" /\ pc[q$1] = "cs"))

================================================================================
