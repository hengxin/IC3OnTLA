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
  @type: ((a291, a292) => (a291 -> a292));
*)
:>(__key, __value) == [ __x \in {__key} |-> __value ]

(*
  @type: (((a270 -> a271), (a270 -> a271)) => (a270 -> a271));
*)
@@(__f1, __f2) ==
  LET (*@type: (() => (a270 -> a271)); *) __f1_cache == __f1 IN
  LET (*@type: (() => (a270 -> a271)); *) __f2_cache == __f2 IN
  LET (*@type: (() => Set(a270)); *) __d1 == DOMAIN __f1_cache IN
  LET (*@type: (() => Set(a270)); *) __d2 == DOMAIN __f2_cache IN
  [
    __x \in __d1 \union __d2 |->
      IF __x \in __d1 THEN (__f1_cache)[__x] ELSE (__f2_cache)[__x]
  ]

(*
  @type: ((Str, a266) => a266);
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
  @type: ((Int) => a257);
*)
TLCGet(__i) ==
  LET (*@type: (() => Set(a259)); *) __Empty == {} IN
  CHOOSE __x \in __Empty: TRUE

(*
  @type: ((Int, a254) => Bool);
*)
TLCSet(__i, __v) == TRUE

(*
  @type: ((Set(a244)) => Set((a244 -> a244)));
*)
Permutations(__S) ==
  { __f \in [__S -> __S]: \A __w \in __S: \E __v \in __S: __f[__v] = __w }

(*
  @type: ((Set(a241)) => a241);
*)
RandomElement(__s) == CHOOSE __x \in __s: TRUE

(*
  @type: (() => a235);
*)
Any ==
  LET (*@type: (() => Set(a237)); *) __Empty == {} IN
  CHOOSE __x \in __Empty: TRUE

(*
  @type: ((a233) => Str);
*)
ToString(__v) == ""

(*
  @type: ((a231) => a231);
*)
TLCEval(__v) == __v

(*
  @type: ((Seq(a184), ((a184, a184) => Bool)) => (Int -> a184));
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
InitializeNODE == Node = { "n1_OF_NODE", "n2_OF_NODE" }

(*
  @type: (() => Bool);
*)
Inv_0 == \A x_0 \in Node: x_0 \in alive \/ ~(x_0 \in go_abort)

(*
  @type: (() => Bool);
*)
Inv_1 == \A x_0 \in Node: x_0 \in alive \/ ~(x_0 \in decide_abort)

(*
  @type: (() => Bool);
*)
Inv_2 == \A x_0 \in Node: x_0 \in go_commit \/ ~(x_0 \in decide_commit)

(*
  @type: (() => Bool);
*)
Inv_3 == \A x_0 \in Node: x_0 \in vote_yes \/ ~(x_0 \in vote_no)

(*
  @type: (() => Bool);
*)
Inv_4 == \A x_0 \in Node: x_0 \in decide_abort \/ ~(x_0 \in decide_commit)

(*
  @type: (() => Bool);
*)
Inv_5 == \A x_0 \in Node: x_0 \in vote_no \/ ~(x_0 \in decide_abort)

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
Inv ==
  (((((((TRUE /\ TypeOK) /\ Inv_0) /\ Inv_1) /\ Inv_2) /\ Inv_3) /\ Inv_4) /\ P)
    /\ Inv_5

================================================================================
