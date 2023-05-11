--------------------------- MODULE 06_OutInlinePass ---------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC, Apalache

CONSTANT
  (*
    @type: Set(RM);
  *)
  RM

VARIABLE
  (*
    @type: Set([rm: RM, type: Str]);
  *)
  msgs

VARIABLE
  (*
    @type: (RM -> Str);
  *)
  rmState

VARIABLE
  (*
    @type: Str;
  *)
  tmState

VARIABLE
  (*
    @type: Set(RM);
  *)
  tmPrepared

(*
  @type: (() => Bool);
*)
InitializeRM == RM = { "r1_OF_RM", "r2_OF_RM" }

(*
  @type: (() => Bool);
*)
Next ==
  ((tmState = "init"
        /\ tmPrepared = RM
        /\ tmState' = "committed"
        /\ msgs' = msgs \union {[type |-> "Commit"]}
        /\ (rmState' := rmState /\ tmPrepared' := tmPrepared))
      \/ (tmState = "init"
        /\ tmState' = "aborted"
        /\ msgs' = msgs \union {[type |-> "Abort"]}
        /\ (rmState' := rmState /\ tmPrepared' := tmPrepared)))
    \/ (\E rm$1 \in RM:
      ((((tmState = "init"
                /\ [type |-> "Prepared", rm |-> rm$1] \in msgs
                /\ tmPrepared' = tmPrepared \union {rm$1}
                /\ (rmState' := rmState /\ tmState' := tmState /\ msgs' := msgs))
              \/ (rmState[rm$1] = "working"
                /\ rmState' = [ rmState EXCEPT ![rm$1] = "prepared" ]
                /\ msgs' = msgs \union {[type |-> "Prepared", rm |-> rm$1]}
                /\ (tmState' := tmState /\ tmPrepared' := tmPrepared)))
            \/ (rmState[rm$1] = "working"
              /\ rmState' = [ rmState EXCEPT ![rm$1] = "aborted" ]
              /\ (tmState' := tmState
                /\ tmPrepared' := tmPrepared
                /\ msgs' := msgs)))
          \/ (([type |-> "Commit"] \in msgs
              /\ rmState' = [ rmState EXCEPT ![rm$1] = "committed" ]
              /\ (tmState' := tmState
                /\ tmPrepared' := tmPrepared
                /\ msgs' := msgs))
            \/ ([type |-> "Abort"] \in msgs
              /\ rmState' = [ rmState EXCEPT ![rm$1] = "aborted" ]
              /\ (tmState' := tmState
                /\ tmPrepared' := tmPrepared
                /\ msgs' := msgs)))))

(*
  @type: (() => Bool);
*)
P ==
  (rmState \in [RM -> { "working", "prepared", "committed", "aborted" }]
      /\ tmState \in { "init", "committed", "aborted" }
      /\ tmPrepared \in SUBSET RM
      /\ msgs
        \in SUBSET ({
          [type |-> t$1, rm |-> r$1]:
            t$1 \in {"Prepared"},
            r$1 \in RM
        }
          \union { [type |-> t$2]: t$2 \in { "Commit", "Abort" } }))
    /\ (\A rm1$1 \in RM:
      \A rm2$1 \in RM:
        ~(rmState[rm1$1] = "aborted" /\ rmState[rm2$1] = "committed"))

(*
  @type: (() => Bool);
*)
Inv ==
  TRUE
    /\ (rmState \in [RM -> { "working", "prepared", "committed", "aborted" }]
      /\ tmState \in { "init", "committed", "aborted" }
      /\ tmPrepared \in SUBSET RM
      /\ msgs
        \in SUBSET ({
          [type |-> t$3, rm |-> r$2]:
            t$3 \in {"Prepared"},
            r$2 \in RM
        }
          \union { [type |-> t$4]: t$4 \in { "Commit", "Abort" } }))

================================================================================
