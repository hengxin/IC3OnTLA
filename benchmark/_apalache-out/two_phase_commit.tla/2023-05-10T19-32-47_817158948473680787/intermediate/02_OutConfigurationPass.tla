------------------------ MODULE 02_OutConfigurationPass ------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC, Apalache

CONSTANT
  (*
    @type: Set(NODE);
  *)
  Node

VARIABLE
  (*
    @type: Set(NODE);
  *)
  vote_yes

VARIABLE
  (*
    @type: Bool;
  *)
  abort_flag

VARIABLE
  (*
    @type: Set(NODE);
  *)
  go_abort

VARIABLE
  (*
    @type: Set(NODE);
  *)
  vote_no

VARIABLE
  (*
    @type: Set(NODE);
  *)
  alive

VARIABLE
  (*
    @type: Set(NODE);
  *)
  decide_abort

VARIABLE
  (*
    @type: Set(NODE);
  *)
  decide_commit

VARIABLE
  (*
    @type: Set(NODE);
  *)
  go_commit

(*
  @type: ((a273, a274) => (a273 -> a274));
*)
:>(__key, __value) == [ __x \in {__key} |-> __value ]

(*
  @type: (((a252 -> a253), (a252 -> a253)) => (a252 -> a253));
*)
@@(__f1, __f2) ==
  LET (*@type: (() => (a252 -> a253)); *) __f1_cache == __f1 IN
  LET (*@type: (() => (a252 -> a253)); *) __f2_cache == __f2 IN
  LET (*@type: (() => Set(a252)); *) __d1 == DOMAIN __f1_cache IN
  LET (*@type: (() => Set(a252)); *) __d2 == DOMAIN __f2_cache IN
  [
    __x \in __d1 \union __d2 |->
      IF __x \in __d1 THEN (__f1_cache)[__x] ELSE (__f2_cache)[__x]
  ]

(*
  @type: ((Str, a248) => a248);
*)
Print(__out, __val) == __val

(*
  @type: ((Str) => Bool);
*)
PrintT(__out) == TRUE

(*
  @type: ((Bool, Str) => Bool);
*)
Assert(__cond, __out) == __cond

(*
  @type: (() => Int);
*)
JavaTime == 123

(*
  @type: ((Int) => a239);
*)
TLCGet(__i) ==
  LET (*@type: (() => Set(a241)); *) __Empty == {} IN
  CHOOSE __x \in __Empty: TRUE

(*
  @type: ((Int, a236) => Bool);
*)
TLCSet(__i, __v) == TRUE

(*
  @type: ((Set(a226)) => Set((a226 -> a226)));
*)
Permutations(__S) ==
  { __f \in [__S -> __S]: \A __w \in __S: \E __v \in __S: __f[__v] = __w }

(*
  @type: ((Set(a223)) => a223);
*)
RandomElement(__s) == CHOOSE __x \in __s: TRUE

(*
  @type: (() => a217);
*)
Any ==
  LET (*@type: (() => Set(a219)); *) __Empty == {} IN
  CHOOSE __x \in __Empty: TRUE

(*
  @type: ((a215) => Str);
*)
ToString(__v) == ""

(*
  @type: ((a213) => a213);
*)
TLCEval(__v) == __v

(*
  @type: ((Seq(a166), ((a166, a166) => Bool)) => (Int -> a166));
*)
SortSeq(__s, __Op(_, _)) ==
  LET (*
    @type: (() => (Int -> Int));
  *)
  __Perm ==
    CHOOSE __p \in Permutations((DOMAIN __s)):
      \A __i \in DOMAIN __s:
        \A __j \in DOMAIN __s:
          (__i < __j => __Op(__s[__p[__i]], __s[__p[__j]]))
            \/ __s[__p[__i]] = __s[__p[__j]]
  IN
  [ __i \in DOMAIN __s |-> __s[(__Perm)[__i]] ]

(*
  @type: (() => <<Set(NODE), Set(NODE), Set(NODE), Set(NODE), Set(NODE), Set(NODE), Set(NODE), Bool>>);
*)
vars ==
  <<
    vote_yes, vote_no, alive, go_commit, go_abort, decide_commit, decide_abort, abort_flag
  >>

(*
  @type: ((NODE) => Bool);
*)
Vote1(n) ==
  n \in alive
    /\ n \notin vote_no
    /\ n \notin decide_commit
    /\ n \notin decide_abort
    /\ vote_yes' = vote_yes \union {n}
    /\ UNCHANGED (<<
      vote_no, alive, go_commit, go_abort, decide_commit, decide_abort, abort_flag
    >>)

(*
  @type: ((NODE) => Bool);
*)
Vote2(n) ==
  n \in alive
    /\ n \notin vote_yes
    /\ n \notin decide_commit
    /\ n \notin decide_abort
    /\ vote_no' = vote_no \union {n}
    /\ abort_flag' = TRUE
    /\ decide_abort' = decide_abort \union {n}
    /\ UNCHANGED (<<vote_yes, alive, go_commit, go_abort, decide_commit>>)

(*
  @type: ((NODE) => Bool);
*)
Fail(n) ==
  n \in alive
    /\ alive' = alive \ {n}
    /\ abort_flag' = TRUE
    /\ UNCHANGED (<<
      vote_yes, vote_no, go_commit, go_abort, decide_commit, decide_abort
    >>)

(*
  @type: (() => Bool);
*)
Go1 ==
  (\A n \in Node: n \notin go_commit)
    /\ (\A n \in Node: n \notin go_abort)
    /\ (\A n \in Node: n \in vote_yes)
    /\ go_commit' = Node
    /\ UNCHANGED (<<
      vote_yes, vote_no, alive, go_abort, decide_commit, decide_abort, abort_flag
    >>)

(*
  @type: (() => Bool);
*)
Go2 ==
  (\A n \in Node: n \notin go_commit)
    /\ (\A n \in Node: n \notin go_abort)
    /\ (\E n \in Node: n \in vote_no \/ n \notin alive)
    /\ go_abort' = Node
    /\ UNCHANGED (<<
      vote_yes, vote_no, alive, go_commit, decide_commit, decide_abort, abort_flag
    >>)

(*
  @type: ((NODE) => Bool);
*)
Commit(n) ==
  n \in alive
    /\ n \in go_commit
    /\ decide_commit' = decide_commit \union {n}
    /\ UNCHANGED (<<
      vote_yes, vote_no, alive, go_commit, go_abort, decide_abort, abort_flag
    >>)

(*
  @type: ((NODE) => Bool);
*)
Abort(n) ==
  n \in alive
    /\ n \in go_abort
    /\ decide_abort' = decide_abort \union {n}
    /\ UNCHANGED (<<
      vote_yes, vote_no, alive, go_commit, go_abort, decide_commit, abort_flag
    >>)

(*
  @type: (() => Bool);
*)
Init ==
  vote_yes = {}
    /\ vote_no = {}
    /\ alive = Node
    /\ go_commit = {}
    /\ go_abort = {}
    /\ decide_commit = {}
    /\ decide_abort = {}
    /\ abort_flag = FALSE

(*
  @type: (() => Bool);
*)
TypeOK ==
  vote_yes \in SUBSET Node
    /\ vote_no \in SUBSET Node
    /\ alive \in SUBSET Node
    /\ go_commit \in SUBSET Node
    /\ go_abort \in SUBSET Node
    /\ decide_commit \in SUBSET Node
    /\ decide_abort \in SUBSET Node
    /\ abort_flag \in BOOLEAN

(*
  @type: (() => Bool);
*)
Safety ==
  (\A n \in Node: \A n2 \in Node: n \in decide_commit => n2 \notin decide_abort)
    /\ (\A n \in Node: \A n2 \in Node: n \in decide_commit => n2 \in vote_yes)
    /\ (\A n \in Node: \A n2 \in Node: n \in decide_abort => abort_flag)

(*
  @type: (() => Set((NODE -> NODE)));
*)
Symmetry == Permutations(Node)

(*
  @type: (() => Bool);
*)
InitializeNODE == Node = { "n1_OF_NODE", "n2_OF_NODE", "n3_OF_NODE" }

(*
  @type: (() => Bool);
*)
Next ==
  (\E n \in Node: Vote1(n))
    \/ (\E n \in Node: Vote2(n))
    \/ (\E n \in Node: Fail(n))
    \/ Go1
    \/ Go2
    \/ (\E n \in Node: Commit(n))
    \/ (\E n \in Node: Abort(n))

(*
  @type: (() => Bool);
*)
NextUnchanged == UNCHANGED vars

(*
  @type: (() => Bool);
*)
P == TypeOK /\ Safety

(*
  @type: (() => Bool);
*)
Inv == TRUE /\ TypeOK

================================================================================
