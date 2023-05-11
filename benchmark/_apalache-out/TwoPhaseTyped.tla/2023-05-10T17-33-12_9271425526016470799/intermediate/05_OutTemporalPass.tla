-------------------------- MODULE 05_OutTemporalPass --------------------------

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
    \/ (\E rm$2 \in RM:
      ((((tmState = "init"
                /\ [type |-> "Prepared", rm |-> rm$2] \in msgs
                /\ tmPrepared' = tmPrepared \union {rm$2}
                /\ (rmState' := rmState /\ tmState' := tmState /\ msgs' := msgs))
              \/ (rmState[rm$2] = "working"
                /\ rmState' = [ rmState EXCEPT ![rm$2] = "prepared" ]
                /\ msgs' = msgs \union {[type |-> "Prepared", rm |-> rm$2]}
                /\ (tmState' := tmState /\ tmPrepared' := tmPrepared)))
            \/ (rmState[rm$2] = "working"
              /\ rmState' = [ rmState EXCEPT ![rm$2] = "aborted" ]
              /\ (tmState' := tmState
                /\ tmPrepared' := tmPrepared
                /\ msgs' := msgs)))
          \/ (([type |-> "Commit"] \in msgs
              /\ rmState' = [ rmState EXCEPT ![rm$2] = "committed" ]
              /\ (tmState' := tmState
                /\ tmPrepared' := tmPrepared
                /\ msgs' := msgs))
            \/ ([type |-> "Abort"] \in msgs
              /\ rmState' = [ rmState EXCEPT ![rm$2] = "aborted" ]
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
          [type |-> t$5, rm |-> r$3]:
            t$5 \in {"Prepared"},
            r$3 \in RM
        }
          \union { [type |-> t$6]: t$6 \in { "Commit", "Abort" } }))
    /\ (\A rm1$2 \in RM:
      \A rm2$2 \in RM:
        ~(rmState[rm1$2] = "aborted" /\ rmState[rm2$2] = "committed"))

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
          [type |-> t$7, rm |-> r$4]:
            t$7 \in {"Prepared"},
            r$4 \in RM
        }
          \union { [type |-> t$8]: t$8 \in { "Commit", "Abort" } }))

================================================================================
