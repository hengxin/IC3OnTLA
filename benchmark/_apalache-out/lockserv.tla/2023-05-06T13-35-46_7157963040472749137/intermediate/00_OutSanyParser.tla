--------------------------- MODULE 00_OutSanyParser ---------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC, Apalache

CONSTANT
  (*
    @type: Set(NODE);
  *)
  Node

VARIABLE
  (*
    @type: NODE -> Bool;
  *)
  lock_msg

VARIABLE
  (*
    @type: Bool;
  *)
  server_holds_lock

VARIABLE
  (*
    @type: NODE -> Bool;
  *)
  holds_lock

VARIABLE
  (*
    @type: NODE -> Bool;
  *)
  grant_msg

VARIABLE
  (*
    @type: NODE -> Bool;
  *)
  unlock_msg

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

vars == <<lock_msg, grant_msg, unlock_msg, holds_lock, server_holds_lock>>

SendLock(n) ==
  lock_msg' = [ lock_msg EXCEPT ![n] = TRUE ]
    /\ UNCHANGED (<<unlock_msg, grant_msg, holds_lock, server_holds_lock>>)

RecvLock(n) ==
  server_holds_lock
    /\ lock_msg[n]
    /\ server_holds_lock' = FALSE
    /\ lock_msg' = [ k \in Node |-> lock_msg[k] /\ k /= n ]
    /\ grant_msg' = [ grant_msg EXCEPT ![n] = TRUE ]
    /\ UNCHANGED (<<unlock_msg, holds_lock>>)

RecvGrant(n) ==
  grant_msg[n]
    /\ grant_msg' = [ k \in Node |-> grant_msg[k] /\ k /= n ]
    /\ holds_lock' = [ holds_lock EXCEPT ![n] = TRUE ]
    /\ UNCHANGED (<<lock_msg, unlock_msg, server_holds_lock>>)

Unlock(n) ==
  holds_lock[n]
    /\ holds_lock' = [ k \in Node |-> holds_lock[k] /\ k /= n ]
    /\ unlock_msg' = [ unlock_msg EXCEPT ![n] = TRUE ]
    /\ UNCHANGED (<<lock_msg, grant_msg, server_holds_lock>>)

RecvUnlock(n) ==
  unlock_msg[n]
    /\ unlock_msg' = [ k \in Node |-> unlock_msg[k] /\ k /= n ]
    /\ server_holds_lock' = TRUE
    /\ UNCHANGED (<<lock_msg, grant_msg, holds_lock>>)

Init ==
  lock_msg = [ n \in Node |-> FALSE ]
    /\ unlock_msg = [ n \in Node |-> FALSE ]
    /\ grant_msg = [ n \in Node |-> FALSE ]
    /\ holds_lock = [ n \in Node |-> FALSE ]
    /\ server_holds_lock = TRUE

TypeOK ==
  lock_msg \in [Node -> BOOLEAN]
    /\ grant_msg \in [Node -> BOOLEAN]
    /\ unlock_msg \in [Node -> BOOLEAN]
    /\ holds_lock \in [Node -> BOOLEAN]
    /\ server_holds_lock \in BOOLEAN

(*
  No two clients think they hold the lock simultaneously.
*)
Mutex == \A x \in Node: \A y \in Node: holds_lock[x] /\ holds_lock[y] => x = y

InitializeNode == Node = { "n1_OF_NODE", "n2_OF_NODE", "n3_OF_NODE" }

Next ==
  (\E n \in Node: SendLock(n))
    \/ (\E n \in Node: RecvLock(n))
    \/ (\E n \in Node: RecvGrant(n))
    \/ (\E n \in Node: Unlock(n))
    \/ (\E n \in Node: RecvUnlock(n))

NextUnchanged == UNCHANGED vars

P == TypeOK /\ Mutex

================================================================================
