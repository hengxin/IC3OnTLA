--------------------------- MODULE 00_OutSanyParser ---------------------------

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
  The famous smiley operator.
  @type: (a, b) => (a -> b);
*)
:>(__key, __value) == [ __x \in {__key} |-> __value ]

(*
  Function composition (fun-fun).
  @type: (a -> b, a -> b) => (a -> b);
*)
@@(__f1, __f2) ==
  LET __f1_cache == __f1 IN
  LET __f2_cache == __f2 IN
  LET __d1 == DOMAIN __f1_cache IN
  LET __d2 == DOMAIN __f2_cache IN
  [
    __x \in __d1 \union __d2 |->
      IF __x \in __d1 THEN (__f1_cache)[__x] ELSE (__f2_cache)[__x]
  ]

(*
  Print is doing nothing in Apalache.
  @type: (Str, a) => a;
*)
Print(__out, __val) == __val

(*
  Print is doing nothing in Apalache.
  @type: Str => Bool;
*)
PrintT(__out) == TRUE

(*
  In Apalache, assert is side-effect free.
 It never produces an error, even if the condition is false.
  @type: (Bool, Str) => Bool;
*)
Assert(__cond, __out) == __cond

(*
  Apalache does not support this operator, but the type checker does.
  @type: () => Int;
*)
JavaTime == 123

(*
  Apalache does not support this operator, but the type checker does.
  @type: Int => a;
*)
TLCGet(__i) ==
  LET (*@type: () => Set(a); *) __Empty == {} IN CHOOSE __x \in __Empty: TRUE

(*
  Apalache does not support this operator, but the type checker does.
  @type: (Int, a) => Bool;
*)
TLCSet(__i, __v) == TRUE

(*
  @type: Set(a) => Set(a -> a);
*)
Permutations(__S) ==
  { __f \in [__S -> __S]: \A __w \in __S: \E __v \in __S: __f[__v] = __w }

(*
  Obviously, we cannot do randomization in Apalache.
  @type: Set(a) => a;
*)
RandomElement(__s) == CHOOSE __x \in __s: TRUE

(*
  Most likely, the type checker will fail on that one more often than it will work.
  @type: () => a;
*)
Any ==
  LET (*@type: () => Set(a); *) __Empty == {} IN CHOOSE __x \in __Empty: TRUE

(*
  @type: a => Str;
*)
ToString(__v) == ""

(*
  For type compatibility with TLC.
  @type: a => a;
*)
TLCEval(__v) == __v

(*
  We return the function instead of a sequence, because that is what it returns.
  @type: (Seq(a), (a, a) => Bool) => (Int -> a);
*)
SortSeq(__s, __Op(_, _)) ==
  LET __Perm ==
    CHOOSE __p \in Permutations((DOMAIN __s)):
      \A __i \in DOMAIN __s:
        \A __j \in DOMAIN __s:
          (__i < __j => __Op(__s[__p[__i]], __s[__p[__j]]))
            \/ __s[__p[__i]] = __s[__p[__j]]
  IN
  [ __i \in DOMAIN __s |-> __s[(__Perm)[__i]] ]

vars ==
  <<
    vote_yes, vote_no, alive, go_commit, go_abort, decide_commit, decide_abort, abort_flag
  >>

Vote1(n) ==
  n \in alive
    /\ n \notin vote_no
    /\ n \notin decide_commit
    /\ n \notin decide_abort
    /\ vote_yes' = vote_yes \union {n}
    /\ UNCHANGED (<<
      vote_no, alive, go_commit, go_abort, decide_commit, decide_abort, abort_flag
    >>)

Vote2(n) ==
  n \in alive
    /\ n \notin vote_yes
    /\ n \notin decide_commit
    /\ n \notin decide_abort
    /\ vote_no' = vote_no \union {n}
    /\ abort_flag' = TRUE
    /\ decide_abort' = decide_abort \union {n}
    /\ UNCHANGED (<<vote_yes, alive, go_commit, go_abort, decide_commit>>)

Fail(n) ==
  n \in alive
    /\ alive' = alive \ {n}
    /\ abort_flag' = TRUE
    /\ UNCHANGED (<<
      vote_yes, vote_no, go_commit, go_abort, decide_commit, decide_abort
    >>)

Go1 ==
  (\A n \in Node: n \notin go_commit)
    /\ (\A n \in Node: n \notin go_abort)
    /\ (\A n \in Node: n \in vote_yes)
    /\ go_commit' = Node
    /\ UNCHANGED (<<
      vote_yes, vote_no, alive, go_abort, decide_commit, decide_abort, abort_flag
    >>)

Go2 ==
  (\A n \in Node: n \notin go_commit)
    /\ (\A n \in Node: n \notin go_abort)
    /\ (\E n \in Node: n \in vote_no \/ n \notin alive)
    /\ go_abort' = Node
    /\ UNCHANGED (<<
      vote_yes, vote_no, alive, go_commit, decide_commit, decide_abort, abort_flag
    >>)

Commit(n) ==
  n \in alive
    /\ n \in go_commit
    /\ decide_commit' = decide_commit \union {n}
    /\ UNCHANGED (<<
      vote_yes, vote_no, alive, go_commit, go_abort, decide_abort, abort_flag
    >>)

Abort(n) ==
  n \in alive
    /\ n \in go_abort
    /\ decide_abort' = decide_abort \union {n}
    /\ UNCHANGED (<<
      vote_yes, vote_no, alive, go_commit, go_abort, decide_commit, abort_flag
    >>)

Init ==
  vote_yes = {}
    /\ vote_no = {}
    /\ alive = Node
    /\ go_commit = {}
    /\ go_abort = {}
    /\ decide_commit = {}
    /\ decide_abort = {}
    /\ abort_flag = FALSE

TypeOK ==
  vote_yes \in SUBSET Node
    /\ vote_no \in SUBSET Node
    /\ alive \in SUBSET Node
    /\ go_commit \in SUBSET Node
    /\ go_abort \in SUBSET Node
    /\ decide_commit \in SUBSET Node
    /\ decide_abort \in SUBSET Node
    /\ abort_flag \in BOOLEAN

Safety ==
  (\A n \in Node: \A n2 \in Node: n \in decide_commit => n2 \notin decide_abort)
    /\ (\A n \in Node: \A n2 \in Node: n \in decide_commit => n2 \in vote_yes)
    /\ (\A n \in Node: \A n2 \in Node: n \in decide_abort => abort_flag)

Symmetry == Permutations(Node)

InitializeNODE == Node = { "n1_OF_NODE", "n2_OF_NODE" }

Inv_0 == \A x_0 \in Node: x_0 \in alive \/ ~(x_0 \in go_abort)

Next ==
  (\E n \in Node: Vote1(n))
    \/ (\E n \in Node: Vote2(n))
    \/ (\E n \in Node: Fail(n))
    \/ Go1
    \/ Go2
    \/ (\E n \in Node: Commit(n))
    \/ (\E n \in Node: Abort(n))

NextUnchanged == UNCHANGED vars

P == TypeOK /\ Safety

Inv == (TRUE /\ TypeOK) /\ Inv_0

================================================================================
