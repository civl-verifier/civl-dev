// Boogie program verifier version 2.4.1.10503, Copyright (c) 2003-2014, Microsoft.
// Command Line Options: /noWitnessInference /noCommutativityTriggers /noVerify /CivlDesugaredFile:desugared_files/multiset.desugared.bpl ../multiset.bpl

type X;

const unique null: int;

const unique nil: X;

const unique done: X;

var elt: [int]int;

var valid: [int]bool;

var lock: [int]X;

var owner: [int]X;

const max: int;

function {:builtin "MapConst"} MapConstBool(bool) : [X]bool;

function {:inline} TidCollector(x: X) : [X]bool
{
  MapConstBool(false)[x := true]
}

axiom max > 0;

function {:inline} Inv(valid: [int]bool, elt: [int]int, owner: [int]X) : bool
{
  (forall i: int :: 
    0 <= i && i < max ==> (elt[i] == null <==> !valid[i] && owner[i] == nil))
}

type {:datatype} PendingAsync;

var pendingAsyncMultiset: [PendingAsync]int;

function {:constructor} PendingAsync_acquire(i: int, tid: X) : PendingAsync;

procedure {:inline 1} AddPendingAsync_acquire(i: int, tid: X);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_acquire(i: int, tid: X)
{

  L:
    pendingAsyncMultiset[PendingAsync_acquire(i, tid)] := pendingAsyncMultiset[PendingAsync_acquire(i, tid)] + 1;
    return;
}



function {:constructor} PendingAsync_release(i: int, tid: X) : PendingAsync;

procedure {:inline 1} AddPendingAsync_release(i: int, tid: X);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_release(i: int, tid: X)
{

  L:
    pendingAsyncMultiset[PendingAsync_release(i, tid)] := pendingAsyncMultiset[PendingAsync_release(i, tid)] + 1;
    return;
}



function {:constructor} PendingAsync_getElt(j: int, tid: X) : PendingAsync;

procedure {:inline 1} AddPendingAsync_getElt(j: int, tid: X);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_getElt(j: int, tid: X)
{

  L:
    pendingAsyncMultiset[PendingAsync_getElt(j, tid)] := pendingAsyncMultiset[PendingAsync_getElt(j, tid)] + 1;
    return;
}



function {:constructor} PendingAsync_setElt(j: int, x: int, tid: X) : PendingAsync;

procedure {:inline 1} AddPendingAsync_setElt(j: int, x: int, tid: X);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_setElt(j: int, x: int, tid: X)
{

  L:
    pendingAsyncMultiset[PendingAsync_setElt(j, x, tid)] := pendingAsyncMultiset[PendingAsync_setElt(j, x, tid)] + 1;
    return;
}



function {:constructor} PendingAsync_setEltToNull(j: int, tid: X) : PendingAsync;

procedure {:inline 1} AddPendingAsync_setEltToNull(j: int, tid: X);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_setEltToNull(j: int, tid: X)
{

  L:
    pendingAsyncMultiset[PendingAsync_setEltToNull(j, tid)] := pendingAsyncMultiset[PendingAsync_setEltToNull(j, tid)] + 1;
    return;
}



function {:constructor} PendingAsync_setValid(j: int, tid: X) : PendingAsync;

procedure {:inline 1} AddPendingAsync_setValid(j: int, tid: X);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_setValid(j: int, tid: X)
{

  L:
    pendingAsyncMultiset[PendingAsync_setValid(j, tid)] := pendingAsyncMultiset[PendingAsync_setValid(j, tid)] + 1;
    return;
}



function {:constructor} PendingAsync_isEltThereAndValid(j: int, x: int, tid: X) : PendingAsync;

procedure {:inline 1} AddPendingAsync_isEltThereAndValid(j: int, x: int, tid: X);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_isEltThereAndValid(j: int, x: int, tid: X)
{

  L:
    pendingAsyncMultiset[PendingAsync_isEltThereAndValid(j, x, tid)] := pendingAsyncMultiset[PendingAsync_isEltThereAndValid(j, x, tid)] + 1;
    return;
}



function {:constructor} PendingAsync_FindSlot(x: int, tid: X) : PendingAsync;

procedure {:inline 1} AddPendingAsync_FindSlot(x: int, tid: X);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_FindSlot(x: int, tid: X)
{

  L:
    pendingAsyncMultiset[PendingAsync_FindSlot(x, tid)] := pendingAsyncMultiset[PendingAsync_FindSlot(x, tid)] + 1;
    return;
}



function {:constructor} PendingAsync_Insert(x: int, tid: X) : PendingAsync;

procedure {:inline 1} AddPendingAsync_Insert(x: int, tid: X);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_Insert(x: int, tid: X)
{

  L:
    pendingAsyncMultiset[PendingAsync_Insert(x, tid)] := pendingAsyncMultiset[PendingAsync_Insert(x, tid)] + 1;
    return;
}



function {:constructor} PendingAsync_InsertPair(x: int, y: int, tid: X) : PendingAsync;

procedure {:inline 1} AddPendingAsync_InsertPair(x: int, y: int, tid: X);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_InsertPair(x: int, y: int, tid: X)
{

  L:
    pendingAsyncMultiset[PendingAsync_InsertPair(x, y, tid)] := pendingAsyncMultiset[PendingAsync_InsertPair(x, y, tid)] + 1;
    return;
}



function {:constructor} PendingAsync_LookUp(x: int, tid: X, old_valid: [int]bool, old_elt: [int]int) : PendingAsync;

procedure {:inline 1} AddPendingAsync_LookUp(x: int, tid: X, old_valid: [int]bool, old_elt: [int]int);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_LookUp(x: int, tid: X, old_valid: [int]bool, old_elt: [int]int)
{

  L:
    pendingAsyncMultiset[PendingAsync_LookUp(x, tid, old_valid, old_elt)] := pendingAsyncMultiset[PendingAsync_LookUp(x, tid, old_valid, old_elt)] + 1;
    return;
}



procedure {:inline 1} atomic_acquire_1(i: int, tid: X);
  modifies lock;



procedure {:inline 1} atomic_release_1(i: int, tid: X);
  modifies lock;



procedure {:inline 1} atomic_getElt_1(j: int, tid: X) returns (elt_j: int);



procedure {:inline 1} atomic_setElt_1(j: int, x: int, tid: X);
  modifies elt, owner;



procedure {:inline 1} atomic_setEltToNull_1(j: int, tid: X);
  modifies elt, owner;



procedure {:inline 1} atomic_setValid_1(j: int, tid: X);
  modifies valid, owner;



procedure {:inline 1} atomic_isEltThereAndValid_1(j: int, x: int, tid: X) returns (fnd: bool);



implementation {:inline 1} atomic_acquire_1(i: int, tid: X)
{
  /*** structured program:
    assert 0 <= i && i < max;
    assert tid != nil && tid != done;
    assume lock[i] == nil;
    lock[i] := tid;
  **** end structured program */

  anon0:
    assume lock[i] == nil;
    lock[i] := tid;
    return;
}



implementation {:inline 1} atomic_release_1(i: int, tid: X)
{
  /*** structured program:
    assert 0 <= i && i < max;
    assert lock[i] == tid;
    assert tid != nil && tid != done;
    lock[i] := nil;
  **** end structured program */

  anon0:
    lock[i] := nil;
    return;
}



implementation {:inline 1} atomic_getElt_1(j: int, tid: X) returns (elt_j: int)
{
  /*** structured program:
    assert 0 <= j && j < max;
    assert tid != nil && tid != done;
    assert lock[j] == tid;
    elt_j := elt[j];
  **** end structured program */

  anon0:
    elt_j := elt[j];
    return;
}



implementation {:inline 1} atomic_setElt_1(j: int, x: int, tid: X)
{
  /*** structured program:
    assert x != null && owner[j] == nil;
    assert 0 <= j && j < max;
    assert lock[j] == tid;
    assert tid != nil && tid != done;
    elt[j] := x;
    owner[j] := tid;
  **** end structured program */

  anon0:
    elt[j] := x;
    owner[j] := tid;
    return;
}



implementation {:inline 1} atomic_setEltToNull_1(j: int, tid: X)
{
  /*** structured program:
    assert owner[j] == tid && lock[j] == tid;
    assert 0 <= j && j < max;
    assert !valid[j];
    assert tid != nil && tid != done;
    elt[j] := null;
    owner[j] := nil;
  **** end structured program */

  anon0:
    elt[j] := null;
    owner[j] := nil;
    return;
}



implementation {:inline 1} atomic_setValid_1(j: int, tid: X)
{
  /*** structured program:
    assert 0 <= j && j < max;
    assert lock[j] == tid;
    assert tid != nil && tid != done;
    assert owner[j] == tid;
    valid[j] := true;
    owner[j] := done;
  **** end structured program */

  anon0:
    valid[j] := true;
    owner[j] := done;
    return;
}



implementation {:inline 1} atomic_isEltThereAndValid_1(j: int, x: int, tid: X) returns (fnd: bool)
{
  /*** structured program:
    assert 0 <= j && j < max;
    assert lock[j] == tid;
    assert tid != nil && tid != done;
    fnd := elt[j] == x && valid[j];
  **** end structured program */

  anon0:
    fnd := elt[j] == x && valid[j];
    return;
}



procedure {:inline 1} atomic_acquire_2(i: int, tid: X);
  modifies lock;



procedure {:inline 1} atomic_release_2(i: int, tid: X);
  modifies lock;



procedure {:inline 1} atomic_setEltToNull_2(j: int, tid: X);
  modifies elt, owner;



procedure {:inline 1} atomic_setValid_2(j: int, tid: X);
  modifies valid, owner;



procedure {:inline 1} atomic_isEltThereAndValid_2(j: int, x: int, tid: X) returns (fnd: bool);



procedure {:inline 1} AtomicFindSlot_2(x: int, tid: X) returns (r: int);
  modifies elt, owner;



implementation {:inline 1} atomic_acquire_2(i: int, tid: X)
{
  /*** structured program:
    assert 0 <= i && i < max;
    assert tid != nil && tid != done;
    assume lock[i] == nil;
    lock[i] := tid;
  **** end structured program */

  anon0:
    assume lock[i] == nil;
    lock[i] := tid;
    return;
}



implementation {:inline 1} atomic_release_2(i: int, tid: X)
{
  /*** structured program:
    assert 0 <= i && i < max;
    assert lock[i] == tid;
    assert tid != nil && tid != done;
    lock[i] := nil;
  **** end structured program */

  anon0:
    lock[i] := nil;
    return;
}



implementation {:inline 1} atomic_setEltToNull_2(j: int, tid: X)
{
  /*** structured program:
    assert owner[j] == tid && lock[j] == tid;
    assert 0 <= j && j < max;
    assert !valid[j];
    assert tid != nil && tid != done;
    elt[j] := null;
    owner[j] := nil;
  **** end structured program */

  anon0:
    elt[j] := null;
    owner[j] := nil;
    return;
}



implementation {:inline 1} atomic_setValid_2(j: int, tid: X)
{
  /*** structured program:
    assert 0 <= j && j < max;
    assert lock[j] == tid;
    assert tid != nil && tid != done;
    assert owner[j] == tid;
    valid[j] := true;
    owner[j] := done;
  **** end structured program */

  anon0:
    valid[j] := true;
    owner[j] := done;
    return;
}



implementation {:inline 1} atomic_isEltThereAndValid_2(j: int, x: int, tid: X) returns (fnd: bool)
{
  /*** structured program:
    assert 0 <= j && j < max;
    assert lock[j] == tid;
    assert tid != nil && tid != done;
    fnd := elt[j] == x && valid[j];
  **** end structured program */

  anon0:
    fnd := elt[j] == x && valid[j];
    return;
}



implementation {:inline 1} AtomicFindSlot_2(x: int, tid: X) returns (r: int)
{
  /*** structured program:
    assert tid != nil && tid != done;
    assert x != null;
    if (*)
    {
        assume 0 <= r && r < max;
        assume elt[r] == null;
        assume owner[r] == nil;
        assume !valid[r];
        elt[r] := x;
        owner[r] := tid;
    }
    else
    {
        assume r == -1;
    }
  **** end structured program */

  anon0:
    goto anon3_Then, anon3_Else;

  anon3_Else:
    assume r == -1;
    return;

  anon3_Then:
    assume 0 <= r && r < max;
    assume elt[r] == null;
    assume owner[r] == nil;
    assume !valid[r];
    elt[r] := x;
    owner[r] := tid;
    return;
}



procedure {:inline 1} AtomicInsert_3(x: int, tid: X) returns (result: bool);
  modifies elt, valid, owner;



procedure {:inline 1} AtomicInsertPair_3(x: int, y: int, tid: X) returns (result: bool);
  modifies elt, valid, owner;



procedure {:inline 1} AtomicLookUp_3(x: int, tid: X, old_valid: [int]bool, old_elt: [int]int) returns (found: bool);



implementation {:inline 1} AtomicInsert_3(x: int, tid: X) returns (result: bool)
{
  var r: int;

  /*** structured program:
    if (*)
    {
        assume 0 <= r && r < max;
        assume valid[r] <==> false;
        assume elt[r] == null;
        assume owner[r] == nil;
        elt[r] := x;
        valid[r] := true;
        owner[r] := done;
        result := true;
    }
    else
    {
        result := false;
    }
  **** end structured program */

  anon0:
    goto anon3_Then, anon3_Else;

  anon3_Else:
    result := false;
    return;

  anon3_Then:
    assume 0 <= r && r < max;
    assume valid[r] <==> false;
    assume elt[r] == null;
    assume owner[r] == nil;
    elt[r] := x;
    valid[r] := true;
    owner[r] := done;
    result := true;
    return;
}



implementation {:inline 1} AtomicInsertPair_3(x: int, y: int, tid: X) returns (result: bool)
{
  var rx: int;
  var ry: int;

  /*** structured program:
    if (*)
    {
        assume 0 <= rx && rx < max && 0 <= ry && ry < max && rx != ry;
        assume valid[rx] <==> false;
        assume valid[ry] <==> false;
        assume elt[rx] == null;
        assume elt[rx] == null;
        elt[rx] := x;
        elt[ry] := y;
        valid[rx] := true;
        valid[ry] := true;
        owner[rx] := done;
        owner[ry] := done;
        result := true;
    }
    else
    {
        result := false;
    }
  **** end structured program */

  anon0:
    goto anon3_Then, anon3_Else;

  anon3_Else:
    result := false;
    return;

  anon3_Then:
    assume 0 <= rx && rx < max && 0 <= ry && ry < max && rx != ry;
    assume valid[rx] <==> false;
    assume valid[ry] <==> false;
    assume elt[rx] == null;
    assume elt[rx] == null;
    elt[rx] := x;
    elt[ry] := y;
    valid[rx] := true;
    valid[ry] := true;
    owner[rx] := done;
    owner[ry] := done;
    result := true;
    return;
}



implementation {:inline 1} AtomicLookUp_3(x: int, tid: X, old_valid: [int]bool, old_elt: [int]int) returns (found: bool)
{
  /*** structured program:
    assert tid != nil && tid != done;
    assert x != null;
    assume found ==> (exists ii: int :: 0 <= ii && ii < max && valid[ii] && elt[ii] == x);
    assume !found
       ==> (forall ii: int :: 0 <= ii && ii < max ==> !(old_valid[ii] && old_elt[ii] == x));
  **** end structured program */

  anon0:
    assume found ==> (exists ii: int :: 0 <= ii && ii < max && valid[ii] && elt[ii] == x);
    assume !found
       ==> (forall ii: int :: 0 <= ii && ii < max ==> !(old_valid[ii] && old_elt[ii] == x));
    return;
}



var linear_tid_hole: [X]bool;

function linear_tid_MapConstBool(b: bool) : [X]bool;

function linear_tid_MapConstInt(b: int) : [X]int;

function linear_tid_MapEq(a: [X]int, b: [X]int) : [X]bool;

function linear_tid_MapImp(a: [X]bool, b: [X]bool) : [X]bool;

function linear_tid_MapOr(a: [X]bool, b: [X]bool) : [X]bool;

axiom (forall a: [X]bool, b: [X]bool :: 
  { linear_tid_MapOr(a, b) } 
  (forall x: X :: linear_tid_MapOr(a, b)[x] <==> a[x] || b[x]));

axiom (forall a: [X]bool, b: [X]bool :: 
  { linear_tid_MapImp(a, b) } 
  (forall x: X :: linear_tid_MapImp(a, b)[x] <==> a[x] ==> b[x]));

axiom (forall x: X :: linear_tid_MapConstBool(true)[x]);

axiom (forall x: X :: !linear_tid_MapConstBool(false)[x]);

axiom (forall a: [X]int, b: [X]int :: 
  { linear_tid_MapEq(a, b) } 
  (forall x: X :: linear_tid_MapEq(a, b)[x] <==> a[x] == b[x]));

axiom (forall a: int, x: X :: linear_tid_MapConstInt(a)[x] == a);

implementation CommutativityChecker_atomic_acquire_1_atomic_acquire_1(first_i: int, first_tid: X, second_i: int, second_tid: X)
{

  first_anon0:
    assume lock[first_i] == nil;
    lock[first_i] := first_tid;
    goto second_anon0;

  second_anon0:
    assume lock[second_i] == nil;
    lock[second_i] := second_tid;
    return;
}



procedure CommutativityChecker_atomic_acquire_1_atomic_acquire_1(first_i: int, first_tid: X, second_i: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= first_i && first_i < max;
  requires first_tid != nil && first_tid != done;
  requires 0 <= second_i && second_i < max;
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> lock == old(lock)[second_i := second_tid][first_i := first_tid]
       && old(lock)[second_i := second_tid][first_i] == nil
       && old(lock)[second_i] == nil;



implementation CommutativityChecker_atomic_acquire_1_atomic_release_1(first_i: int, first_tid: X, second_i: int, second_tid: X)
{

  first_anon0:
    assume lock[first_i] == nil;
    lock[first_i] := first_tid;
    goto second_anon0;

  second_anon0:
    lock[second_i] := nil;
    return;
}



procedure CommutativityChecker_atomic_acquire_1_atomic_release_1(first_i: int, first_tid: X, second_i: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= first_i && first_i < max;
  requires first_tid != nil && first_tid != done;
  requires 0 <= second_i && second_i < max;
  requires lock[second_i] == second_tid;
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> lock == old(lock)[second_i := nil][first_i := first_tid]
       && old(lock)[second_i := nil][first_i] == nil;



implementation GatePreservationChecker_atomic_release_1_atomic_acquire_1(first_i: int, first_tid: X, second_i: int, second_tid: X)
{

  second_anon0:
    assume lock[second_i] == nil;
    lock[second_i] := second_tid;
    return;
}



procedure GatePreservationChecker_atomic_release_1_atomic_acquire_1(first_i: int, first_tid: X, second_i: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= second_i && second_i < max;
  requires second_tid != nil && second_tid != done;
  requires 0 <= first_i && first_i < max;
  requires lock[first_i] == first_tid;
  requires first_tid != nil && first_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> 0 <= first_i && first_i < max;
  ensures true ==> lock[first_i] == first_tid;
  ensures true ==> first_tid != nil && first_tid != done;



implementation GatePreservationChecker_atomic_getElt_1_atomic_acquire_1(first_j: int, first_tid: X, second_i: int, second_tid: X)
   returns (first_elt_j: int)
{

  second_anon0:
    assume lock[second_i] == nil;
    lock[second_i] := second_tid;
    return;
}



procedure GatePreservationChecker_atomic_getElt_1_atomic_acquire_1(first_j: int, first_tid: X, second_i: int, second_tid: X)
   returns (first_elt_j: int);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= second_i && second_i < max;
  requires second_tid != nil && second_tid != done;
  requires 0 <= first_j && first_j < max;
  requires first_tid != nil && first_tid != done;
  requires lock[first_j] == first_tid;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> 0 <= first_j && first_j < max;
  ensures true ==> first_tid != nil && first_tid != done;
  ensures true ==> lock[first_j] == first_tid;



implementation GatePreservationChecker_atomic_setElt_1_atomic_acquire_1(first_j: int, first_x: int, first_tid: X, second_i: int, second_tid: X)
{

  second_anon0:
    assume lock[second_i] == nil;
    lock[second_i] := second_tid;
    return;
}



procedure GatePreservationChecker_atomic_setElt_1_atomic_acquire_1(first_j: int, first_x: int, first_tid: X, second_i: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= second_i && second_i < max;
  requires second_tid != nil && second_tid != done;
  requires first_x != null && owner[first_j] == nil;
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> first_x != null && owner[first_j] == nil;
  ensures true ==> 0 <= first_j && first_j < max;
  ensures true ==> lock[first_j] == first_tid;
  ensures true ==> first_tid != nil && first_tid != done;



implementation GatePreservationChecker_atomic_setEltToNull_1_atomic_acquire_1(first_j: int, first_tid: X, second_i: int, second_tid: X)
{

  second_anon0:
    assume lock[second_i] == nil;
    lock[second_i] := second_tid;
    return;
}



procedure GatePreservationChecker_atomic_setEltToNull_1_atomic_acquire_1(first_j: int, first_tid: X, second_i: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= second_i && second_i < max;
  requires second_tid != nil && second_tid != done;
  requires owner[first_j] == first_tid && lock[first_j] == first_tid;
  requires 0 <= first_j && first_j < max;
  requires !valid[first_j];
  requires first_tid != nil && first_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> owner[first_j] == first_tid && lock[first_j] == first_tid;
  ensures true ==> 0 <= first_j && first_j < max;
  ensures true ==> !valid[first_j];
  ensures true ==> first_tid != nil && first_tid != done;



implementation GatePreservationChecker_atomic_setValid_1_atomic_acquire_1(first_j: int, first_tid: X, second_i: int, second_tid: X)
{

  second_anon0:
    assume lock[second_i] == nil;
    lock[second_i] := second_tid;
    return;
}



procedure GatePreservationChecker_atomic_setValid_1_atomic_acquire_1(first_j: int, first_tid: X, second_i: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= second_i && second_i < max;
  requires second_tid != nil && second_tid != done;
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  requires owner[first_j] == first_tid;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> 0 <= first_j && first_j < max;
  ensures true ==> lock[first_j] == first_tid;
  ensures true ==> first_tid != nil && first_tid != done;
  ensures true ==> owner[first_j] == first_tid;



implementation GatePreservationChecker_atomic_isEltThereAndValid_1_atomic_acquire_1(first_j: int, first_x: int, first_tid: X, second_i: int, second_tid: X)
   returns (first_fnd: bool)
{

  second_anon0:
    assume lock[second_i] == nil;
    lock[second_i] := second_tid;
    return;
}



procedure GatePreservationChecker_atomic_isEltThereAndValid_1_atomic_acquire_1(first_j: int, first_x: int, first_tid: X, second_i: int, second_tid: X)
   returns (first_fnd: bool);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= second_i && second_i < max;
  requires second_tid != nil && second_tid != done;
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> 0 <= first_j && first_j < max;
  ensures true ==> lock[first_j] == first_tid;
  ensures true ==> first_tid != nil && first_tid != done;



implementation CommutativityChecker_atomic_release_1_atomic_release_1(first_i: int, first_tid: X, second_i: int, second_tid: X)
{

  first_anon0:
    lock[first_i] := nil;
    goto second_anon0;

  second_anon0:
    lock[second_i] := nil;
    return;
}



procedure CommutativityChecker_atomic_release_1_atomic_release_1(first_i: int, first_tid: X, second_i: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= first_i && first_i < max;
  requires lock[first_i] == first_tid;
  requires first_tid != nil && first_tid != done;
  requires 0 <= second_i && second_i < max;
  requires lock[second_i] == second_tid;
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> lock == old(lock)[second_i := nil][first_i := nil];



implementation GatePreservationChecker_atomic_release_1_atomic_release_1(first_i: int, first_tid: X, second_i: int, second_tid: X)
{

  second_anon0:
    lock[second_i] := nil;
    return;
}



procedure GatePreservationChecker_atomic_release_1_atomic_release_1(first_i: int, first_tid: X, second_i: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= second_i && second_i < max;
  requires lock[second_i] == second_tid;
  requires second_tid != nil && second_tid != done;
  requires 0 <= first_i && first_i < max;
  requires lock[first_i] == first_tid;
  requires first_tid != nil && first_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> 0 <= first_i && first_i < max;
  ensures true ==> lock[first_i] == first_tid;
  ensures true ==> first_tid != nil && first_tid != done;



implementation FailurePreservationChecker_atomic_release_1_atomic_release_1(first_i: int, first_tid: X, second_i: int, second_tid: X)
{

  second_anon0:
    lock[second_i] := nil;
    return;
}



procedure FailurePreservationChecker_atomic_release_1_atomic_release_1(first_i: int, first_tid: X, second_i: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires !(
    0 <= first_i
     && first_i < max
     && lock[first_i] == first_tid
     && 
    first_tid != nil
     && first_tid != done);
  requires 0 <= second_i && second_i < max;
  requires lock[second_i] == second_tid;
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> !(
      0 <= first_i
       && first_i < max
       && lock[first_i] == first_tid
       && 
      first_tid != nil
       && first_tid != done);



implementation FailurePreservationChecker_atomic_getElt_1_atomic_release_1(first_j: int, first_tid: X, second_i: int, second_tid: X)
   returns (first_elt_j: int)
{

  second_anon0:
    lock[second_i] := nil;
    return;
}



procedure FailurePreservationChecker_atomic_getElt_1_atomic_release_1(first_j: int, first_tid: X, second_i: int, second_tid: X)
   returns (first_elt_j: int);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires !(
    0 <= first_j
     && first_j < max
     && 
    first_tid != nil
     && first_tid != done
     && lock[first_j] == first_tid);
  requires 0 <= second_i && second_i < max;
  requires lock[second_i] == second_tid;
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> !(
      0 <= first_j
       && first_j < max
       && 
      first_tid != nil
       && first_tid != done
       && lock[first_j] == first_tid);



implementation FailurePreservationChecker_atomic_setElt_1_atomic_release_1(first_j: int, first_x: int, first_tid: X, second_i: int, second_tid: X)
{

  second_anon0:
    lock[second_i] := nil;
    return;
}



procedure FailurePreservationChecker_atomic_setElt_1_atomic_release_1(first_j: int, first_x: int, first_tid: X, second_i: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires !(
    first_x != null
     && owner[first_j] == nil
     && 
    0 <= first_j
     && first_j < max
     && lock[first_j] == first_tid
     && 
    first_tid != nil
     && first_tid != done);
  requires 0 <= second_i && second_i < max;
  requires lock[second_i] == second_tid;
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> !(
      first_x != null
       && owner[first_j] == nil
       && 
      0 <= first_j
       && first_j < max
       && lock[first_j] == first_tid
       && 
      first_tid != nil
       && first_tid != done);



implementation FailurePreservationChecker_atomic_setEltToNull_1_atomic_release_1(first_j: int, first_tid: X, second_i: int, second_tid: X)
{

  second_anon0:
    lock[second_i] := nil;
    return;
}



procedure FailurePreservationChecker_atomic_setEltToNull_1_atomic_release_1(first_j: int, first_tid: X, second_i: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires !(
    owner[first_j] == first_tid
     && lock[first_j] == first_tid
     && 
    0 <= first_j
     && first_j < max
     && !valid[first_j]
     && 
    first_tid != nil
     && first_tid != done);
  requires 0 <= second_i && second_i < max;
  requires lock[second_i] == second_tid;
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> !(
      owner[first_j] == first_tid
       && lock[first_j] == first_tid
       && 
      0 <= first_j
       && first_j < max
       && !valid[first_j]
       && 
      first_tid != nil
       && first_tid != done);



implementation FailurePreservationChecker_atomic_setValid_1_atomic_release_1(first_j: int, first_tid: X, second_i: int, second_tid: X)
{

  second_anon0:
    lock[second_i] := nil;
    return;
}



procedure FailurePreservationChecker_atomic_setValid_1_atomic_release_1(first_j: int, first_tid: X, second_i: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires !(
    0 <= first_j
     && first_j < max
     && lock[first_j] == first_tid
     && 
    first_tid != nil
     && first_tid != done
     && owner[first_j] == first_tid);
  requires 0 <= second_i && second_i < max;
  requires lock[second_i] == second_tid;
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> !(
      0 <= first_j
       && first_j < max
       && lock[first_j] == first_tid
       && 
      first_tid != nil
       && first_tid != done
       && owner[first_j] == first_tid);



implementation FailurePreservationChecker_atomic_isEltThereAndValid_1_atomic_release_1(first_j: int, first_x: int, first_tid: X, second_i: int, second_tid: X)
   returns (first_fnd: bool)
{

  second_anon0:
    lock[second_i] := nil;
    return;
}



procedure FailurePreservationChecker_atomic_isEltThereAndValid_1_atomic_release_1(first_j: int, first_x: int, first_tid: X, second_i: int, second_tid: X)
   returns (first_fnd: bool);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires !(
    0 <= first_j
     && first_j < max
     && lock[first_j] == first_tid
     && 
    first_tid != nil
     && first_tid != done);
  requires 0 <= second_i && second_i < max;
  requires lock[second_i] == second_tid;
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> !(
      0 <= first_j
       && first_j < max
       && lock[first_j] == first_tid
       && 
      first_tid != nil
       && first_tid != done);



implementation GatePreservationChecker_atomic_getElt_1_atomic_release_1(first_j: int, first_tid: X, second_i: int, second_tid: X)
   returns (first_elt_j: int)
{

  second_anon0:
    lock[second_i] := nil;
    return;
}



procedure GatePreservationChecker_atomic_getElt_1_atomic_release_1(first_j: int, first_tid: X, second_i: int, second_tid: X)
   returns (first_elt_j: int);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= second_i && second_i < max;
  requires lock[second_i] == second_tid;
  requires second_tid != nil && second_tid != done;
  requires 0 <= first_j && first_j < max;
  requires first_tid != nil && first_tid != done;
  requires lock[first_j] == first_tid;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> 0 <= first_j && first_j < max;
  ensures true ==> first_tid != nil && first_tid != done;
  ensures true ==> lock[first_j] == first_tid;



implementation CommutativityChecker_atomic_getElt_1_atomic_setElt_1(first_j: int, first_tid: X, second_j: int, second_x: int, second_tid: X)
   returns (first_elt_j: int)
{

  first_anon0:
    first_elt_j := elt[first_j];
    goto second_anon0;

  second_anon0:
    elt[second_j] := second_x;
    owner[second_j] := second_tid;
    return;
}



procedure CommutativityChecker_atomic_getElt_1_atomic_setElt_1(first_j: int, first_tid: X, second_j: int, second_x: int, second_tid: X)
   returns (first_elt_j: int);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= first_j && first_j < max;
  requires first_tid != nil && first_tid != done;
  requires lock[first_j] == first_tid;
  requires second_x != null && owner[second_j] == nil;
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> lock == old(lock)
       && elt == old(elt)[second_j := second_x]
       && owner == old(owner)[second_j := second_tid]
       && first_elt_j == old(elt)[second_j := second_x][first_j];



implementation CommutativityChecker_atomic_setElt_1_atomic_getElt_1(first_j: int, first_x: int, first_tid: X, second_j: int, second_tid: X)
   returns (second_elt_j: int)
{

  first_anon0:
    elt[first_j] := first_x;
    owner[first_j] := first_tid;
    goto second_anon0;

  second_anon0:
    second_elt_j := elt[second_j];
    return;
}



procedure CommutativityChecker_atomic_setElt_1_atomic_getElt_1(first_j: int, first_x: int, first_tid: X, second_j: int, second_tid: X)
   returns (second_elt_j: int);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires first_x != null && owner[first_j] == nil;
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  requires 0 <= second_j && second_j < max;
  requires second_tid != nil && second_tid != done;
  requires lock[second_j] == second_tid;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> owner == old(owner)[first_j := first_tid]
       && lock == old(lock)
       && elt == old(elt)[first_j := first_x]
       && second_elt_j == old(elt)[second_j];



implementation CommutativityChecker_atomic_getElt_1_atomic_setEltToNull_1(first_j: int, first_tid: X, second_j: int, second_tid: X)
   returns (first_elt_j: int)
{

  first_anon0:
    first_elt_j := elt[first_j];
    goto second_anon0;

  second_anon0:
    elt[second_j] := null;
    owner[second_j] := nil;
    return;
}



procedure CommutativityChecker_atomic_getElt_1_atomic_setEltToNull_1(first_j: int, first_tid: X, second_j: int, second_tid: X)
   returns (first_elt_j: int);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= first_j && first_j < max;
  requires first_tid != nil && first_tid != done;
  requires lock[first_j] == first_tid;
  requires owner[second_j] == second_tid && lock[second_j] == second_tid;
  requires 0 <= second_j && second_j < max;
  requires !valid[second_j];
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> lock == old(lock)
       && elt == old(elt)[second_j := null]
       && owner == old(owner)[second_j := nil]
       && valid == old(valid)
       && first_elt_j == old(elt)[second_j := null][first_j];



implementation CommutativityChecker_atomic_setEltToNull_1_atomic_getElt_1(first_j: int, first_tid: X, second_j: int, second_tid: X)
   returns (second_elt_j: int)
{

  first_anon0:
    elt[first_j] := null;
    owner[first_j] := nil;
    goto second_anon0;

  second_anon0:
    second_elt_j := elt[second_j];
    return;
}



procedure CommutativityChecker_atomic_setEltToNull_1_atomic_getElt_1(first_j: int, first_tid: X, second_j: int, second_tid: X)
   returns (second_elt_j: int);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires owner[first_j] == first_tid && lock[first_j] == first_tid;
  requires 0 <= first_j && first_j < max;
  requires !valid[first_j];
  requires first_tid != nil && first_tid != done;
  requires 0 <= second_j && second_j < max;
  requires second_tid != nil && second_tid != done;
  requires lock[second_j] == second_tid;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> owner == old(owner)[first_j := nil]
       && lock == old(lock)
       && valid == old(valid)
       && elt == old(elt)[first_j := null]
       && second_elt_j == old(elt)[second_j];



implementation GatePreservationChecker_atomic_setElt_1_atomic_release_1(first_j: int, first_x: int, first_tid: X, second_i: int, second_tid: X)
{

  second_anon0:
    lock[second_i] := nil;
    return;
}



procedure GatePreservationChecker_atomic_setElt_1_atomic_release_1(first_j: int, first_x: int, first_tid: X, second_i: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= second_i && second_i < max;
  requires lock[second_i] == second_tid;
  requires second_tid != nil && second_tid != done;
  requires first_x != null && owner[first_j] == nil;
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> first_x != null && owner[first_j] == nil;
  ensures true ==> 0 <= first_j && first_j < max;
  ensures true ==> lock[first_j] == first_tid;
  ensures true ==> first_tid != nil && first_tid != done;



implementation CommutativityChecker_atomic_setElt_1_atomic_setElt_1(first_j: int, 
    first_x: int, 
    first_tid: X, 
    second_j: int, 
    second_x: int, 
    second_tid: X)
{

  first_anon0:
    elt[first_j] := first_x;
    owner[first_j] := first_tid;
    goto second_anon0;

  second_anon0:
    elt[second_j] := second_x;
    owner[second_j] := second_tid;
    return;
}



procedure CommutativityChecker_atomic_setElt_1_atomic_setElt_1(first_j: int, 
    first_x: int, 
    first_tid: X, 
    second_j: int, 
    second_x: int, 
    second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires first_x != null && owner[first_j] == nil;
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  requires second_x != null && owner[second_j] == nil;
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> owner == old(owner)[second_j := second_tid][first_j := first_tid]
       && lock == old(lock)
       && elt == old(elt)[second_j := second_x][first_j := first_x];



implementation GatePreservationChecker_atomic_setElt_1_atomic_setElt_1(first_j: int, 
    first_x: int, 
    first_tid: X, 
    second_j: int, 
    second_x: int, 
    second_tid: X)
{

  second_anon0:
    elt[second_j] := second_x;
    owner[second_j] := second_tid;
    return;
}



procedure GatePreservationChecker_atomic_setElt_1_atomic_setElt_1(first_j: int, 
    first_x: int, 
    first_tid: X, 
    second_j: int, 
    second_x: int, 
    second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires second_x != null && owner[second_j] == nil;
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  requires first_x != null && owner[first_j] == nil;
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> first_x != null && owner[first_j] == nil;
  ensures true ==> 0 <= first_j && first_j < max;
  ensures true ==> lock[first_j] == first_tid;
  ensures true ==> first_tid != nil && first_tid != done;



implementation FailurePreservationChecker_atomic_setElt_1_atomic_setElt_1(first_j: int, 
    first_x: int, 
    first_tid: X, 
    second_j: int, 
    second_x: int, 
    second_tid: X)
{

  second_anon0:
    elt[second_j] := second_x;
    owner[second_j] := second_tid;
    return;
}



procedure FailurePreservationChecker_atomic_setElt_1_atomic_setElt_1(first_j: int, 
    first_x: int, 
    first_tid: X, 
    second_j: int, 
    second_x: int, 
    second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires !(
    first_x != null
     && owner[first_j] == nil
     && 
    0 <= first_j
     && first_j < max
     && lock[first_j] == first_tid
     && 
    first_tid != nil
     && first_tid != done);
  requires second_x != null && owner[second_j] == nil;
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> !(
      first_x != null
       && owner[first_j] == nil
       && 
      0 <= first_j
       && first_j < max
       && lock[first_j] == first_tid
       && 
      first_tid != nil
       && first_tid != done);



implementation CommutativityChecker_atomic_setElt_1_atomic_setEltToNull_1(first_j: int, first_x: int, first_tid: X, second_j: int, second_tid: X)
{

  first_anon0:
    elt[first_j] := first_x;
    owner[first_j] := first_tid;
    goto second_anon0;

  second_anon0:
    elt[second_j] := null;
    owner[second_j] := nil;
    return;
}



procedure CommutativityChecker_atomic_setElt_1_atomic_setEltToNull_1(first_j: int, first_x: int, first_tid: X, second_j: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires first_x != null && owner[first_j] == nil;
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  requires owner[second_j] == second_tid && lock[second_j] == second_tid;
  requires 0 <= second_j && second_j < max;
  requires !valid[second_j];
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> owner == old(owner)[second_j := nil][first_j := first_tid]
       && lock == old(lock)
       && elt == old(elt)[second_j := null][first_j := first_x]
       && valid == old(valid);



implementation GatePreservationChecker_atomic_setEltToNull_1_atomic_setElt_1(first_j: int, first_tid: X, second_j: int, second_x: int, second_tid: X)
{

  second_anon0:
    elt[second_j] := second_x;
    owner[second_j] := second_tid;
    return;
}



procedure GatePreservationChecker_atomic_setEltToNull_1_atomic_setElt_1(first_j: int, first_tid: X, second_j: int, second_x: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires second_x != null && owner[second_j] == nil;
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  requires owner[first_j] == first_tid && lock[first_j] == first_tid;
  requires 0 <= first_j && first_j < max;
  requires !valid[first_j];
  requires first_tid != nil && first_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> owner[first_j] == first_tid && lock[first_j] == first_tid;
  ensures true ==> 0 <= first_j && first_j < max;
  ensures true ==> !valid[first_j];
  ensures true ==> first_tid != nil && first_tid != done;



implementation CommutativityChecker_atomic_setEltToNull_1_atomic_setElt_1(first_j: int, first_tid: X, second_j: int, second_x: int, second_tid: X)
{

  first_anon0:
    elt[first_j] := null;
    owner[first_j] := nil;
    goto second_anon0;

  second_anon0:
    elt[second_j] := second_x;
    owner[second_j] := second_tid;
    return;
}



procedure CommutativityChecker_atomic_setEltToNull_1_atomic_setElt_1(first_j: int, first_tid: X, second_j: int, second_x: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires owner[first_j] == first_tid && lock[first_j] == first_tid;
  requires 0 <= first_j && first_j < max;
  requires !valid[first_j];
  requires first_tid != nil && first_tid != done;
  requires second_x != null && owner[second_j] == nil;
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> owner == old(owner)[second_j := second_tid][first_j := nil]
       && lock == old(lock)
       && valid == old(valid)
       && elt == old(elt)[second_j := second_x][first_j := null];



implementation GatePreservationChecker_atomic_setElt_1_atomic_setEltToNull_1(first_j: int, first_x: int, first_tid: X, second_j: int, second_tid: X)
{

  second_anon0:
    elt[second_j] := null;
    owner[second_j] := nil;
    return;
}



procedure GatePreservationChecker_atomic_setElt_1_atomic_setEltToNull_1(first_j: int, first_x: int, first_tid: X, second_j: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires owner[second_j] == second_tid && lock[second_j] == second_tid;
  requires 0 <= second_j && second_j < max;
  requires !valid[second_j];
  requires second_tid != nil && second_tid != done;
  requires first_x != null && owner[first_j] == nil;
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> first_x != null && owner[first_j] == nil;
  ensures true ==> 0 <= first_j && first_j < max;
  ensures true ==> lock[first_j] == first_tid;
  ensures true ==> first_tid != nil && first_tid != done;



implementation FailurePreservationChecker_atomic_setEltToNull_1_atomic_setElt_1(first_j: int, first_tid: X, second_j: int, second_x: int, second_tid: X)
{

  second_anon0:
    elt[second_j] := second_x;
    owner[second_j] := second_tid;
    return;
}



procedure FailurePreservationChecker_atomic_setEltToNull_1_atomic_setElt_1(first_j: int, first_tid: X, second_j: int, second_x: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires !(
    owner[first_j] == first_tid
     && lock[first_j] == first_tid
     && 
    0 <= first_j
     && first_j < max
     && !valid[first_j]
     && 
    first_tid != nil
     && first_tid != done);
  requires second_x != null && owner[second_j] == nil;
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> !(
      owner[first_j] == first_tid
       && lock[first_j] == first_tid
       && 
      0 <= first_j
       && first_j < max
       && !valid[first_j]
       && 
      first_tid != nil
       && first_tid != done);



implementation CommutativityChecker_atomic_setElt_1_atomic_setValid_1(first_j: int, first_x: int, first_tid: X, second_j: int, second_tid: X)
{

  first_anon0:
    elt[first_j] := first_x;
    owner[first_j] := first_tid;
    goto second_anon0;

  second_anon0:
    valid[second_j] := true;
    owner[second_j] := done;
    return;
}



procedure CommutativityChecker_atomic_setElt_1_atomic_setValid_1(first_j: int, first_x: int, first_tid: X, second_j: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires first_x != null && owner[first_j] == nil;
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  requires owner[second_j] == second_tid;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> owner == old(owner)[second_j := done][first_j := first_tid]
       && lock == old(lock)
       && elt == old(elt)[first_j := first_x]
       && valid == old(valid)[second_j := true];



implementation GatePreservationChecker_atomic_setValid_1_atomic_setElt_1(first_j: int, first_tid: X, second_j: int, second_x: int, second_tid: X)
{

  second_anon0:
    elt[second_j] := second_x;
    owner[second_j] := second_tid;
    return;
}



procedure GatePreservationChecker_atomic_setValid_1_atomic_setElt_1(first_j: int, first_tid: X, second_j: int, second_x: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires second_x != null && owner[second_j] == nil;
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  requires owner[first_j] == first_tid;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> 0 <= first_j && first_j < max;
  ensures true ==> lock[first_j] == first_tid;
  ensures true ==> first_tid != nil && first_tid != done;
  ensures true ==> owner[first_j] == first_tid;



implementation CommutativityChecker_atomic_setValid_1_atomic_setElt_1(first_j: int, first_tid: X, second_j: int, second_x: int, second_tid: X)
{

  first_anon0:
    valid[first_j] := true;
    owner[first_j] := done;
    goto second_anon0;

  second_anon0:
    elt[second_j] := second_x;
    owner[second_j] := second_tid;
    return;
}



procedure CommutativityChecker_atomic_setValid_1_atomic_setElt_1(first_j: int, first_tid: X, second_j: int, second_x: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  requires owner[first_j] == first_tid;
  requires second_x != null && owner[second_j] == nil;
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> lock == old(lock)
       && owner == old(owner)[second_j := second_tid][first_j := done]
       && valid == old(valid)[first_j := true]
       && elt == old(elt)[second_j := second_x];



implementation GatePreservationChecker_atomic_setElt_1_atomic_setValid_1(first_j: int, first_x: int, first_tid: X, second_j: int, second_tid: X)
{

  second_anon0:
    valid[second_j] := true;
    owner[second_j] := done;
    return;
}



procedure GatePreservationChecker_atomic_setElt_1_atomic_setValid_1(first_j: int, first_x: int, first_tid: X, second_j: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  requires owner[second_j] == second_tid;
  requires first_x != null && owner[first_j] == nil;
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> first_x != null && owner[first_j] == nil;
  ensures true ==> 0 <= first_j && first_j < max;
  ensures true ==> lock[first_j] == first_tid;
  ensures true ==> first_tid != nil && first_tid != done;



implementation FailurePreservationChecker_atomic_setValid_1_atomic_setElt_1(first_j: int, first_tid: X, second_j: int, second_x: int, second_tid: X)
{

  second_anon0:
    elt[second_j] := second_x;
    owner[second_j] := second_tid;
    return;
}



procedure FailurePreservationChecker_atomic_setValid_1_atomic_setElt_1(first_j: int, first_tid: X, second_j: int, second_x: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires !(
    0 <= first_j
     && first_j < max
     && lock[first_j] == first_tid
     && 
    first_tid != nil
     && first_tid != done
     && owner[first_j] == first_tid);
  requires second_x != null && owner[second_j] == nil;
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> !(
      0 <= first_j
       && first_j < max
       && lock[first_j] == first_tid
       && 
      first_tid != nil
       && first_tid != done
       && owner[first_j] == first_tid);



implementation CommutativityChecker_atomic_setElt_1_atomic_isEltThereAndValid_1(first_j: int, 
    first_x: int, 
    first_tid: X, 
    second_j: int, 
    second_x: int, 
    second_tid: X)
   returns (second_fnd: bool)
{

  first_anon0:
    elt[first_j] := first_x;
    owner[first_j] := first_tid;
    goto second_anon0;

  second_anon0:
    second_fnd := elt[second_j] == second_x && valid[second_j];
    return;
}



procedure CommutativityChecker_atomic_setElt_1_atomic_isEltThereAndValid_1(first_j: int, 
    first_x: int, 
    first_tid: X, 
    second_j: int, 
    second_x: int, 
    second_tid: X)
   returns (second_fnd: bool);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires first_x != null && owner[first_j] == nil;
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> owner == old(owner)[first_j := first_tid]
       && lock == old(lock)
       && elt == old(elt)[first_j := first_x]
       && valid == old(valid)
       && (second_fnd <==> old(elt)[second_j] == second_x && old(valid)[second_j]);



implementation CommutativityChecker_atomic_isEltThereAndValid_1_atomic_setElt_1(first_j: int, 
    first_x: int, 
    first_tid: X, 
    second_j: int, 
    second_x: int, 
    second_tid: X)
   returns (first_fnd: bool)
{

  first_anon0:
    first_fnd := elt[first_j] == first_x && valid[first_j];
    goto second_anon0;

  second_anon0:
    elt[second_j] := second_x;
    owner[second_j] := second_tid;
    return;
}



procedure CommutativityChecker_atomic_isEltThereAndValid_1_atomic_setElt_1(first_j: int, 
    first_x: int, 
    first_tid: X, 
    second_j: int, 
    second_x: int, 
    second_tid: X)
   returns (first_fnd: bool);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  requires second_x != null && owner[second_j] == nil;
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> lock == old(lock)
       && elt == old(elt)[second_j := second_x]
       && valid == old(valid)
       && owner == old(owner)[second_j := second_tid]
       && (first_fnd
         <==> old(elt)[second_j := second_x][first_j] == first_x && old(valid)[first_j]);



implementation GatePreservationChecker_atomic_setEltToNull_1_atomic_release_1(first_j: int, first_tid: X, second_i: int, second_tid: X)
{

  second_anon0:
    lock[second_i] := nil;
    return;
}



procedure GatePreservationChecker_atomic_setEltToNull_1_atomic_release_1(first_j: int, first_tid: X, second_i: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= second_i && second_i < max;
  requires lock[second_i] == second_tid;
  requires second_tid != nil && second_tid != done;
  requires owner[first_j] == first_tid && lock[first_j] == first_tid;
  requires 0 <= first_j && first_j < max;
  requires !valid[first_j];
  requires first_tid != nil && first_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> owner[first_j] == first_tid && lock[first_j] == first_tid;
  ensures true ==> 0 <= first_j && first_j < max;
  ensures true ==> !valid[first_j];
  ensures true ==> first_tid != nil && first_tid != done;



implementation FailurePreservationChecker_atomic_setElt_1_atomic_setEltToNull_1(first_j: int, first_x: int, first_tid: X, second_j: int, second_tid: X)
{

  second_anon0:
    elt[second_j] := null;
    owner[second_j] := nil;
    return;
}



procedure FailurePreservationChecker_atomic_setElt_1_atomic_setEltToNull_1(first_j: int, first_x: int, first_tid: X, second_j: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires !(
    first_x != null
     && owner[first_j] == nil
     && 
    0 <= first_j
     && first_j < max
     && lock[first_j] == first_tid
     && 
    first_tid != nil
     && first_tid != done);
  requires owner[second_j] == second_tid && lock[second_j] == second_tid;
  requires 0 <= second_j && second_j < max;
  requires !valid[second_j];
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> !(
      first_x != null
       && owner[first_j] == nil
       && 
      0 <= first_j
       && first_j < max
       && lock[first_j] == first_tid
       && 
      first_tid != nil
       && first_tid != done);



implementation CommutativityChecker_atomic_setEltToNull_1_atomic_setEltToNull_1(first_j: int, first_tid: X, second_j: int, second_tid: X)
{

  first_anon0:
    elt[first_j] := null;
    owner[first_j] := nil;
    goto second_anon0;

  second_anon0:
    elt[second_j] := null;
    owner[second_j] := nil;
    return;
}



procedure CommutativityChecker_atomic_setEltToNull_1_atomic_setEltToNull_1(first_j: int, first_tid: X, second_j: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires owner[first_j] == first_tid && lock[first_j] == first_tid;
  requires 0 <= first_j && first_j < max;
  requires !valid[first_j];
  requires first_tid != nil && first_tid != done;
  requires owner[second_j] == second_tid && lock[second_j] == second_tid;
  requires 0 <= second_j && second_j < max;
  requires !valid[second_j];
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> owner == old(owner)[second_j := nil][first_j := nil]
       && lock == old(lock)
       && valid == old(valid)
       && elt == old(elt)[second_j := null][first_j := null];



implementation GatePreservationChecker_atomic_setEltToNull_1_atomic_setEltToNull_1(first_j: int, first_tid: X, second_j: int, second_tid: X)
{

  second_anon0:
    elt[second_j] := null;
    owner[second_j] := nil;
    return;
}



procedure GatePreservationChecker_atomic_setEltToNull_1_atomic_setEltToNull_1(first_j: int, first_tid: X, second_j: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires owner[second_j] == second_tid && lock[second_j] == second_tid;
  requires 0 <= second_j && second_j < max;
  requires !valid[second_j];
  requires second_tid != nil && second_tid != done;
  requires owner[first_j] == first_tid && lock[first_j] == first_tid;
  requires 0 <= first_j && first_j < max;
  requires !valid[first_j];
  requires first_tid != nil && first_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> owner[first_j] == first_tid && lock[first_j] == first_tid;
  ensures true ==> 0 <= first_j && first_j < max;
  ensures true ==> !valid[first_j];
  ensures true ==> first_tid != nil && first_tid != done;



implementation FailurePreservationChecker_atomic_setEltToNull_1_atomic_setEltToNull_1(first_j: int, first_tid: X, second_j: int, second_tid: X)
{

  second_anon0:
    elt[second_j] := null;
    owner[second_j] := nil;
    return;
}



procedure FailurePreservationChecker_atomic_setEltToNull_1_atomic_setEltToNull_1(first_j: int, first_tid: X, second_j: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires !(
    owner[first_j] == first_tid
     && lock[first_j] == first_tid
     && 
    0 <= first_j
     && first_j < max
     && !valid[first_j]
     && 
    first_tid != nil
     && first_tid != done);
  requires owner[second_j] == second_tid && lock[second_j] == second_tid;
  requires 0 <= second_j && second_j < max;
  requires !valid[second_j];
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> !(
      owner[first_j] == first_tid
       && lock[first_j] == first_tid
       && 
      0 <= first_j
       && first_j < max
       && !valid[first_j]
       && 
      first_tid != nil
       && first_tid != done);



implementation CommutativityChecker_atomic_setValid_1_atomic_setEltToNull_1(first_j: int, first_tid: X, second_j: int, second_tid: X)
{

  first_anon0:
    valid[first_j] := true;
    owner[first_j] := done;
    goto second_anon0;

  second_anon0:
    elt[second_j] := null;
    owner[second_j] := nil;
    return;
}



procedure CommutativityChecker_atomic_setValid_1_atomic_setEltToNull_1(first_j: int, first_tid: X, second_j: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  requires owner[first_j] == first_tid;
  requires owner[second_j] == second_tid && lock[second_j] == second_tid;
  requires 0 <= second_j && second_j < max;
  requires !valid[second_j];
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> lock == old(lock)
       && owner == old(owner)[second_j := nil][first_j := done]
       && valid == old(valid)[first_j := true]
       && elt == old(elt)[second_j := null];



implementation GatePreservationChecker_atomic_setEltToNull_1_atomic_setValid_1(first_j: int, first_tid: X, second_j: int, second_tid: X)
{

  second_anon0:
    valid[second_j] := true;
    owner[second_j] := done;
    return;
}



procedure GatePreservationChecker_atomic_setEltToNull_1_atomic_setValid_1(first_j: int, first_tid: X, second_j: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  requires owner[second_j] == second_tid;
  requires owner[first_j] == first_tid && lock[first_j] == first_tid;
  requires 0 <= first_j && first_j < max;
  requires !valid[first_j];
  requires first_tid != nil && first_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> owner[first_j] == first_tid && lock[first_j] == first_tid;
  ensures true ==> 0 <= first_j && first_j < max;
  ensures true ==> !valid[first_j];
  ensures true ==> first_tid != nil && first_tid != done;



implementation FailurePreservationChecker_atomic_setValid_1_atomic_setEltToNull_1(first_j: int, first_tid: X, second_j: int, second_tid: X)
{

  second_anon0:
    elt[second_j] := null;
    owner[second_j] := nil;
    return;
}



procedure FailurePreservationChecker_atomic_setValid_1_atomic_setEltToNull_1(first_j: int, first_tid: X, second_j: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires !(
    0 <= first_j
     && first_j < max
     && lock[first_j] == first_tid
     && 
    first_tid != nil
     && first_tid != done
     && owner[first_j] == first_tid);
  requires owner[second_j] == second_tid && lock[second_j] == second_tid;
  requires 0 <= second_j && second_j < max;
  requires !valid[second_j];
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> !(
      0 <= first_j
       && first_j < max
       && lock[first_j] == first_tid
       && 
      first_tid != nil
       && first_tid != done
       && owner[first_j] == first_tid);



implementation CommutativityChecker_atomic_isEltThereAndValid_1_atomic_setEltToNull_1(first_j: int, first_x: int, first_tid: X, second_j: int, second_tid: X)
   returns (first_fnd: bool)
{

  first_anon0:
    first_fnd := elt[first_j] == first_x && valid[first_j];
    goto second_anon0;

  second_anon0:
    elt[second_j] := null;
    owner[second_j] := nil;
    return;
}



procedure CommutativityChecker_atomic_isEltThereAndValid_1_atomic_setEltToNull_1(first_j: int, first_x: int, first_tid: X, second_j: int, second_tid: X)
   returns (first_fnd: bool);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  requires owner[second_j] == second_tid && lock[second_j] == second_tid;
  requires 0 <= second_j && second_j < max;
  requires !valid[second_j];
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> lock == old(lock)
       && elt == old(elt)[second_j := null]
       && valid == old(valid)
       && owner == old(owner)[second_j := nil]
       && (first_fnd
         <==> old(elt)[second_j := null][first_j] == first_x && old(valid)[first_j]);



implementation GatePreservationChecker_atomic_setValid_1_atomic_release_1(first_j: int, first_tid: X, second_i: int, second_tid: X)
{

  second_anon0:
    lock[second_i] := nil;
    return;
}



procedure GatePreservationChecker_atomic_setValid_1_atomic_release_1(first_j: int, first_tid: X, second_i: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= second_i && second_i < max;
  requires lock[second_i] == second_tid;
  requires second_tid != nil && second_tid != done;
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  requires owner[first_j] == first_tid;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> 0 <= first_j && first_j < max;
  ensures true ==> lock[first_j] == first_tid;
  ensures true ==> first_tid != nil && first_tid != done;
  ensures true ==> owner[first_j] == first_tid;



implementation FailurePreservationChecker_atomic_setElt_1_atomic_setValid_1(first_j: int, first_x: int, first_tid: X, second_j: int, second_tid: X)
{

  second_anon0:
    valid[second_j] := true;
    owner[second_j] := done;
    return;
}



procedure FailurePreservationChecker_atomic_setElt_1_atomic_setValid_1(first_j: int, first_x: int, first_tid: X, second_j: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires !(
    first_x != null
     && owner[first_j] == nil
     && 
    0 <= first_j
     && first_j < max
     && lock[first_j] == first_tid
     && 
    first_tid != nil
     && first_tid != done);
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  requires owner[second_j] == second_tid;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> !(
      first_x != null
       && owner[first_j] == nil
       && 
      0 <= first_j
       && first_j < max
       && lock[first_j] == first_tid
       && 
      first_tid != nil
       && first_tid != done);



implementation CommutativityChecker_atomic_setEltToNull_1_atomic_setValid_1(first_j: int, first_tid: X, second_j: int, second_tid: X)
{

  first_anon0:
    elt[first_j] := null;
    owner[first_j] := nil;
    goto second_anon0;

  second_anon0:
    valid[second_j] := true;
    owner[second_j] := done;
    return;
}



procedure CommutativityChecker_atomic_setEltToNull_1_atomic_setValid_1(first_j: int, first_tid: X, second_j: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires owner[first_j] == first_tid && lock[first_j] == first_tid;
  requires 0 <= first_j && first_j < max;
  requires !valid[first_j];
  requires first_tid != nil && first_tid != done;
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  requires owner[second_j] == second_tid;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> owner == old(owner)[second_j := done][first_j := nil]
       && lock == old(lock)
       && valid == old(valid)[second_j := true]
       && elt == old(elt)[first_j := null];



implementation GatePreservationChecker_atomic_setValid_1_atomic_setEltToNull_1(first_j: int, first_tid: X, second_j: int, second_tid: X)
{

  second_anon0:
    elt[second_j] := null;
    owner[second_j] := nil;
    return;
}



procedure GatePreservationChecker_atomic_setValid_1_atomic_setEltToNull_1(first_j: int, first_tid: X, second_j: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires owner[second_j] == second_tid && lock[second_j] == second_tid;
  requires 0 <= second_j && second_j < max;
  requires !valid[second_j];
  requires second_tid != nil && second_tid != done;
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  requires owner[first_j] == first_tid;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> 0 <= first_j && first_j < max;
  ensures true ==> lock[first_j] == first_tid;
  ensures true ==> first_tid != nil && first_tid != done;
  ensures true ==> owner[first_j] == first_tid;



implementation FailurePreservationChecker_atomic_setEltToNull_1_atomic_setValid_1(first_j: int, first_tid: X, second_j: int, second_tid: X)
{

  second_anon0:
    valid[second_j] := true;
    owner[second_j] := done;
    return;
}



procedure FailurePreservationChecker_atomic_setEltToNull_1_atomic_setValid_1(first_j: int, first_tid: X, second_j: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires !(
    owner[first_j] == first_tid
     && lock[first_j] == first_tid
     && 
    0 <= first_j
     && first_j < max
     && !valid[first_j]
     && 
    first_tid != nil
     && first_tid != done);
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  requires owner[second_j] == second_tid;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> !(
      owner[first_j] == first_tid
       && lock[first_j] == first_tid
       && 
      0 <= first_j
       && first_j < max
       && !valid[first_j]
       && 
      first_tid != nil
       && first_tid != done);



implementation CommutativityChecker_atomic_setValid_1_atomic_setValid_1(first_j: int, first_tid: X, second_j: int, second_tid: X)
{

  first_anon0:
    valid[first_j] := true;
    owner[first_j] := done;
    goto second_anon0;

  second_anon0:
    valid[second_j] := true;
    owner[second_j] := done;
    return;
}



procedure CommutativityChecker_atomic_setValid_1_atomic_setValid_1(first_j: int, first_tid: X, second_j: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  requires owner[first_j] == first_tid;
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  requires owner[second_j] == second_tid;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> lock == old(lock)
       && owner == old(owner)[second_j := done][first_j := done]
       && valid == old(valid)[second_j := true][first_j := true];



implementation GatePreservationChecker_atomic_setValid_1_atomic_setValid_1(first_j: int, first_tid: X, second_j: int, second_tid: X)
{

  second_anon0:
    valid[second_j] := true;
    owner[second_j] := done;
    return;
}



procedure GatePreservationChecker_atomic_setValid_1_atomic_setValid_1(first_j: int, first_tid: X, second_j: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  requires owner[second_j] == second_tid;
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  requires owner[first_j] == first_tid;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> 0 <= first_j && first_j < max;
  ensures true ==> lock[first_j] == first_tid;
  ensures true ==> first_tid != nil && first_tid != done;
  ensures true ==> owner[first_j] == first_tid;



implementation FailurePreservationChecker_atomic_setValid_1_atomic_setValid_1(first_j: int, first_tid: X, second_j: int, second_tid: X)
{

  second_anon0:
    valid[second_j] := true;
    owner[second_j] := done;
    return;
}



procedure FailurePreservationChecker_atomic_setValid_1_atomic_setValid_1(first_j: int, first_tid: X, second_j: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires !(
    0 <= first_j
     && first_j < max
     && lock[first_j] == first_tid
     && 
    first_tid != nil
     && first_tid != done
     && owner[first_j] == first_tid);
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  requires owner[second_j] == second_tid;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> !(
      0 <= first_j
       && first_j < max
       && lock[first_j] == first_tid
       && 
      first_tid != nil
       && first_tid != done
       && owner[first_j] == first_tid);



implementation CommutativityChecker_atomic_setValid_1_atomic_isEltThereAndValid_1(first_j: int, first_tid: X, second_j: int, second_x: int, second_tid: X)
   returns (second_fnd: bool)
{

  first_anon0:
    valid[first_j] := true;
    owner[first_j] := done;
    goto second_anon0;

  second_anon0:
    second_fnd := elt[second_j] == second_x && valid[second_j];
    return;
}



procedure CommutativityChecker_atomic_setValid_1_atomic_isEltThereAndValid_1(first_j: int, first_tid: X, second_j: int, second_x: int, second_tid: X)
   returns (second_fnd: bool);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  requires owner[first_j] == first_tid;
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> lock == old(lock)
       && owner == old(owner)[first_j := done]
       && valid == old(valid)[first_j := true]
       && elt == old(elt)
       && (second_fnd <==> old(elt)[second_j] == second_x && old(valid)[second_j]);



implementation CommutativityChecker_atomic_isEltThereAndValid_1_atomic_setValid_1(first_j: int, first_x: int, first_tid: X, second_j: int, second_tid: X)
   returns (first_fnd: bool)
{

  first_anon0:
    first_fnd := elt[first_j] == first_x && valid[first_j];
    goto second_anon0;

  second_anon0:
    valid[second_j] := true;
    owner[second_j] := done;
    return;
}



procedure CommutativityChecker_atomic_isEltThereAndValid_1_atomic_setValid_1(first_j: int, first_x: int, first_tid: X, second_j: int, second_tid: X)
   returns (first_fnd: bool);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  requires owner[second_j] == second_tid;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> lock == old(lock)
       && elt == old(elt)
       && valid == old(valid)[second_j := true]
       && owner == old(owner)[second_j := done]
       && (first_fnd
         <==> old(elt)[first_j] == first_x && old(valid)[second_j := true][first_j]);



implementation GatePreservationChecker_atomic_isEltThereAndValid_1_atomic_release_1(first_j: int, first_x: int, first_tid: X, second_i: int, second_tid: X)
   returns (first_fnd: bool)
{

  second_anon0:
    lock[second_i] := nil;
    return;
}



procedure GatePreservationChecker_atomic_isEltThereAndValid_1_atomic_release_1(first_j: int, first_x: int, first_tid: X, second_i: int, second_tid: X)
   returns (first_fnd: bool);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= second_i && second_i < max;
  requires lock[second_i] == second_tid;
  requires second_tid != nil && second_tid != done;
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> 0 <= first_j && first_j < max;
  ensures true ==> lock[first_j] == first_tid;
  ensures true ==> first_tid != nil && first_tid != done;



implementation CommutativityChecker_atomic_setEltToNull_1_atomic_isEltThereAndValid_1(first_j: int, first_tid: X, second_j: int, second_x: int, second_tid: X)
   returns (second_fnd: bool)
{

  first_anon0:
    elt[first_j] := null;
    owner[first_j] := nil;
    goto second_anon0;

  second_anon0:
    second_fnd := elt[second_j] == second_x && valid[second_j];
    return;
}



procedure CommutativityChecker_atomic_setEltToNull_1_atomic_isEltThereAndValid_1(first_j: int, first_tid: X, second_j: int, second_x: int, second_tid: X)
   returns (second_fnd: bool);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires owner[first_j] == first_tid && lock[first_j] == first_tid;
  requires 0 <= first_j && first_j < max;
  requires !valid[first_j];
  requires first_tid != nil && first_tid != done;
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> owner == old(owner)[first_j := nil]
       && lock == old(lock)
       && valid == old(valid)
       && elt == old(elt)[first_j := null]
       && (second_fnd <==> old(elt)[second_j] == second_x && old(valid)[second_j]);



implementation CommutativityChecker_atomic_acquire_2_atomic_acquire_2(first_i: int, first_tid: X, second_i: int, second_tid: X)
{

  first_anon0:
    assume lock[first_i] == nil;
    lock[first_i] := first_tid;
    goto second_anon0;

  second_anon0:
    assume lock[second_i] == nil;
    lock[second_i] := second_tid;
    return;
}



procedure CommutativityChecker_atomic_acquire_2_atomic_acquire_2(first_i: int, first_tid: X, second_i: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= first_i && first_i < max;
  requires first_tid != nil && first_tid != done;
  requires 0 <= second_i && second_i < max;
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> lock == old(lock)[second_i := second_tid][first_i := first_tid]
       && old(lock)[second_i := second_tid][first_i] == nil
       && old(lock)[second_i] == nil;



implementation CommutativityChecker_atomic_acquire_2_atomic_release_2(first_i: int, first_tid: X, second_i: int, second_tid: X)
{

  first_anon0:
    assume lock[first_i] == nil;
    lock[first_i] := first_tid;
    goto second_anon0;

  second_anon0:
    lock[second_i] := nil;
    return;
}



procedure CommutativityChecker_atomic_acquire_2_atomic_release_2(first_i: int, first_tid: X, second_i: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= first_i && first_i < max;
  requires first_tid != nil && first_tid != done;
  requires 0 <= second_i && second_i < max;
  requires lock[second_i] == second_tid;
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> lock == old(lock)[second_i := nil][first_i := first_tid]
       && old(lock)[second_i := nil][first_i] == nil;



implementation GatePreservationChecker_atomic_release_2_atomic_acquire_2(first_i: int, first_tid: X, second_i: int, second_tid: X)
{

  second_anon0:
    assume lock[second_i] == nil;
    lock[second_i] := second_tid;
    return;
}



procedure GatePreservationChecker_atomic_release_2_atomic_acquire_2(first_i: int, first_tid: X, second_i: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= second_i && second_i < max;
  requires second_tid != nil && second_tid != done;
  requires 0 <= first_i && first_i < max;
  requires lock[first_i] == first_tid;
  requires first_tid != nil && first_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> 0 <= first_i && first_i < max;
  ensures true ==> lock[first_i] == first_tid;
  ensures true ==> first_tid != nil && first_tid != done;



implementation GatePreservationChecker_atomic_setEltToNull_2_atomic_acquire_2(first_j: int, first_tid: X, second_i: int, second_tid: X)
{

  second_anon0:
    assume lock[second_i] == nil;
    lock[second_i] := second_tid;
    return;
}



procedure GatePreservationChecker_atomic_setEltToNull_2_atomic_acquire_2(first_j: int, first_tid: X, second_i: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= second_i && second_i < max;
  requires second_tid != nil && second_tid != done;
  requires owner[first_j] == first_tid && lock[first_j] == first_tid;
  requires 0 <= first_j && first_j < max;
  requires !valid[first_j];
  requires first_tid != nil && first_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> owner[first_j] == first_tid && lock[first_j] == first_tid;
  ensures true ==> 0 <= first_j && first_j < max;
  ensures true ==> !valid[first_j];
  ensures true ==> first_tid != nil && first_tid != done;



implementation GatePreservationChecker_atomic_setValid_2_atomic_acquire_2(first_j: int, first_tid: X, second_i: int, second_tid: X)
{

  second_anon0:
    assume lock[second_i] == nil;
    lock[second_i] := second_tid;
    return;
}



procedure GatePreservationChecker_atomic_setValid_2_atomic_acquire_2(first_j: int, first_tid: X, second_i: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= second_i && second_i < max;
  requires second_tid != nil && second_tid != done;
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  requires owner[first_j] == first_tid;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> 0 <= first_j && first_j < max;
  ensures true ==> lock[first_j] == first_tid;
  ensures true ==> first_tid != nil && first_tid != done;
  ensures true ==> owner[first_j] == first_tid;



implementation GatePreservationChecker_atomic_isEltThereAndValid_2_atomic_acquire_2(first_j: int, first_x: int, first_tid: X, second_i: int, second_tid: X)
   returns (first_fnd: bool)
{

  second_anon0:
    assume lock[second_i] == nil;
    lock[second_i] := second_tid;
    return;
}



procedure GatePreservationChecker_atomic_isEltThereAndValid_2_atomic_acquire_2(first_j: int, first_x: int, first_tid: X, second_i: int, second_tid: X)
   returns (first_fnd: bool);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= second_i && second_i < max;
  requires second_tid != nil && second_tid != done;
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> 0 <= first_j && first_j < max;
  ensures true ==> lock[first_j] == first_tid;
  ensures true ==> first_tid != nil && first_tid != done;



implementation CommutativityChecker_atomic_release_2_atomic_release_2(first_i: int, first_tid: X, second_i: int, second_tid: X)
{

  first_anon0:
    lock[first_i] := nil;
    goto second_anon0;

  second_anon0:
    lock[second_i] := nil;
    return;
}



procedure CommutativityChecker_atomic_release_2_atomic_release_2(first_i: int, first_tid: X, second_i: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= first_i && first_i < max;
  requires lock[first_i] == first_tid;
  requires first_tid != nil && first_tid != done;
  requires 0 <= second_i && second_i < max;
  requires lock[second_i] == second_tid;
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> lock == old(lock)[second_i := nil][first_i := nil];



implementation GatePreservationChecker_atomic_release_2_atomic_release_2(first_i: int, first_tid: X, second_i: int, second_tid: X)
{

  second_anon0:
    lock[second_i] := nil;
    return;
}



procedure GatePreservationChecker_atomic_release_2_atomic_release_2(first_i: int, first_tid: X, second_i: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= second_i && second_i < max;
  requires lock[second_i] == second_tid;
  requires second_tid != nil && second_tid != done;
  requires 0 <= first_i && first_i < max;
  requires lock[first_i] == first_tid;
  requires first_tid != nil && first_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> 0 <= first_i && first_i < max;
  ensures true ==> lock[first_i] == first_tid;
  ensures true ==> first_tid != nil && first_tid != done;



implementation FailurePreservationChecker_atomic_release_2_atomic_release_2(first_i: int, first_tid: X, second_i: int, second_tid: X)
{

  second_anon0:
    lock[second_i] := nil;
    return;
}



procedure FailurePreservationChecker_atomic_release_2_atomic_release_2(first_i: int, first_tid: X, second_i: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires !(
    0 <= first_i
     && first_i < max
     && lock[first_i] == first_tid
     && 
    first_tid != nil
     && first_tid != done);
  requires 0 <= second_i && second_i < max;
  requires lock[second_i] == second_tid;
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> !(
      0 <= first_i
       && first_i < max
       && lock[first_i] == first_tid
       && 
      first_tid != nil
       && first_tid != done);



implementation FailurePreservationChecker_atomic_setEltToNull_2_atomic_release_2(first_j: int, first_tid: X, second_i: int, second_tid: X)
{

  second_anon0:
    lock[second_i] := nil;
    return;
}



procedure FailurePreservationChecker_atomic_setEltToNull_2_atomic_release_2(first_j: int, first_tid: X, second_i: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires !(
    owner[first_j] == first_tid
     && lock[first_j] == first_tid
     && 
    0 <= first_j
     && first_j < max
     && !valid[first_j]
     && 
    first_tid != nil
     && first_tid != done);
  requires 0 <= second_i && second_i < max;
  requires lock[second_i] == second_tid;
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> !(
      owner[first_j] == first_tid
       && lock[first_j] == first_tid
       && 
      0 <= first_j
       && first_j < max
       && !valid[first_j]
       && 
      first_tid != nil
       && first_tid != done);



implementation FailurePreservationChecker_atomic_setValid_2_atomic_release_2(first_j: int, first_tid: X, second_i: int, second_tid: X)
{

  second_anon0:
    lock[second_i] := nil;
    return;
}



procedure FailurePreservationChecker_atomic_setValid_2_atomic_release_2(first_j: int, first_tid: X, second_i: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires !(
    0 <= first_j
     && first_j < max
     && lock[first_j] == first_tid
     && 
    first_tid != nil
     && first_tid != done
     && owner[first_j] == first_tid);
  requires 0 <= second_i && second_i < max;
  requires lock[second_i] == second_tid;
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> !(
      0 <= first_j
       && first_j < max
       && lock[first_j] == first_tid
       && 
      first_tid != nil
       && first_tid != done
       && owner[first_j] == first_tid);



implementation FailurePreservationChecker_atomic_isEltThereAndValid_2_atomic_release_2(first_j: int, first_x: int, first_tid: X, second_i: int, second_tid: X)
   returns (first_fnd: bool)
{

  second_anon0:
    lock[second_i] := nil;
    return;
}



procedure FailurePreservationChecker_atomic_isEltThereAndValid_2_atomic_release_2(first_j: int, first_x: int, first_tid: X, second_i: int, second_tid: X)
   returns (first_fnd: bool);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires !(
    0 <= first_j
     && first_j < max
     && lock[first_j] == first_tid
     && 
    first_tid != nil
     && first_tid != done);
  requires 0 <= second_i && second_i < max;
  requires lock[second_i] == second_tid;
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> !(
      0 <= first_j
       && first_j < max
       && lock[first_j] == first_tid
       && 
      first_tid != nil
       && first_tid != done);



implementation GatePreservationChecker_atomic_setEltToNull_2_atomic_release_2(first_j: int, first_tid: X, second_i: int, second_tid: X)
{

  second_anon0:
    lock[second_i] := nil;
    return;
}



procedure GatePreservationChecker_atomic_setEltToNull_2_atomic_release_2(first_j: int, first_tid: X, second_i: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= second_i && second_i < max;
  requires lock[second_i] == second_tid;
  requires second_tid != nil && second_tid != done;
  requires owner[first_j] == first_tid && lock[first_j] == first_tid;
  requires 0 <= first_j && first_j < max;
  requires !valid[first_j];
  requires first_tid != nil && first_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> owner[first_j] == first_tid && lock[first_j] == first_tid;
  ensures true ==> 0 <= first_j && first_j < max;
  ensures true ==> !valid[first_j];
  ensures true ==> first_tid != nil && first_tid != done;



implementation CommutativityChecker_atomic_setEltToNull_2_atomic_setEltToNull_2(first_j: int, first_tid: X, second_j: int, second_tid: X)
{

  first_anon0:
    elt[first_j] := null;
    owner[first_j] := nil;
    goto second_anon0;

  second_anon0:
    elt[second_j] := null;
    owner[second_j] := nil;
    return;
}



procedure CommutativityChecker_atomic_setEltToNull_2_atomic_setEltToNull_2(first_j: int, first_tid: X, second_j: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires owner[first_j] == first_tid && lock[first_j] == first_tid;
  requires 0 <= first_j && first_j < max;
  requires !valid[first_j];
  requires first_tid != nil && first_tid != done;
  requires owner[second_j] == second_tid && lock[second_j] == second_tid;
  requires 0 <= second_j && second_j < max;
  requires !valid[second_j];
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> owner == old(owner)[second_j := nil][first_j := nil]
       && lock == old(lock)
       && valid == old(valid)
       && elt == old(elt)[second_j := null][first_j := null];



implementation GatePreservationChecker_atomic_setEltToNull_2_atomic_setEltToNull_2(first_j: int, first_tid: X, second_j: int, second_tid: X)
{

  second_anon0:
    elt[second_j] := null;
    owner[second_j] := nil;
    return;
}



procedure GatePreservationChecker_atomic_setEltToNull_2_atomic_setEltToNull_2(first_j: int, first_tid: X, second_j: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires owner[second_j] == second_tid && lock[second_j] == second_tid;
  requires 0 <= second_j && second_j < max;
  requires !valid[second_j];
  requires second_tid != nil && second_tid != done;
  requires owner[first_j] == first_tid && lock[first_j] == first_tid;
  requires 0 <= first_j && first_j < max;
  requires !valid[first_j];
  requires first_tid != nil && first_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> owner[first_j] == first_tid && lock[first_j] == first_tid;
  ensures true ==> 0 <= first_j && first_j < max;
  ensures true ==> !valid[first_j];
  ensures true ==> first_tid != nil && first_tid != done;



implementation FailurePreservationChecker_atomic_setEltToNull_2_atomic_setEltToNull_2(first_j: int, first_tid: X, second_j: int, second_tid: X)
{

  second_anon0:
    elt[second_j] := null;
    owner[second_j] := nil;
    return;
}



procedure FailurePreservationChecker_atomic_setEltToNull_2_atomic_setEltToNull_2(first_j: int, first_tid: X, second_j: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires !(
    owner[first_j] == first_tid
     && lock[first_j] == first_tid
     && 
    0 <= first_j
     && first_j < max
     && !valid[first_j]
     && 
    first_tid != nil
     && first_tid != done);
  requires owner[second_j] == second_tid && lock[second_j] == second_tid;
  requires 0 <= second_j && second_j < max;
  requires !valid[second_j];
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> !(
      owner[first_j] == first_tid
       && lock[first_j] == first_tid
       && 
      0 <= first_j
       && first_j < max
       && !valid[first_j]
       && 
      first_tid != nil
       && first_tid != done);



implementation CommutativityChecker_atomic_setValid_2_atomic_setEltToNull_2(first_j: int, first_tid: X, second_j: int, second_tid: X)
{

  first_anon0:
    valid[first_j] := true;
    owner[first_j] := done;
    goto second_anon0;

  second_anon0:
    elt[second_j] := null;
    owner[second_j] := nil;
    return;
}



procedure CommutativityChecker_atomic_setValid_2_atomic_setEltToNull_2(first_j: int, first_tid: X, second_j: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  requires owner[first_j] == first_tid;
  requires owner[second_j] == second_tid && lock[second_j] == second_tid;
  requires 0 <= second_j && second_j < max;
  requires !valid[second_j];
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> lock == old(lock)
       && owner == old(owner)[second_j := nil][first_j := done]
       && valid == old(valid)[first_j := true]
       && elt == old(elt)[second_j := null];



implementation GatePreservationChecker_atomic_setEltToNull_2_atomic_setValid_2(first_j: int, first_tid: X, second_j: int, second_tid: X)
{

  second_anon0:
    valid[second_j] := true;
    owner[second_j] := done;
    return;
}



procedure GatePreservationChecker_atomic_setEltToNull_2_atomic_setValid_2(first_j: int, first_tid: X, second_j: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  requires owner[second_j] == second_tid;
  requires owner[first_j] == first_tid && lock[first_j] == first_tid;
  requires 0 <= first_j && first_j < max;
  requires !valid[first_j];
  requires first_tid != nil && first_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> owner[first_j] == first_tid && lock[first_j] == first_tid;
  ensures true ==> 0 <= first_j && first_j < max;
  ensures true ==> !valid[first_j];
  ensures true ==> first_tid != nil && first_tid != done;



implementation FailurePreservationChecker_atomic_setValid_2_atomic_setEltToNull_2(first_j: int, first_tid: X, second_j: int, second_tid: X)
{

  second_anon0:
    elt[second_j] := null;
    owner[second_j] := nil;
    return;
}



procedure FailurePreservationChecker_atomic_setValid_2_atomic_setEltToNull_2(first_j: int, first_tid: X, second_j: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires !(
    0 <= first_j
     && first_j < max
     && lock[first_j] == first_tid
     && 
    first_tid != nil
     && first_tid != done
     && owner[first_j] == first_tid);
  requires owner[second_j] == second_tid && lock[second_j] == second_tid;
  requires 0 <= second_j && second_j < max;
  requires !valid[second_j];
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> !(
      0 <= first_j
       && first_j < max
       && lock[first_j] == first_tid
       && 
      first_tid != nil
       && first_tid != done
       && owner[first_j] == first_tid);



implementation CommutativityChecker_atomic_isEltThereAndValid_2_atomic_setEltToNull_2(first_j: int, first_x: int, first_tid: X, second_j: int, second_tid: X)
   returns (first_fnd: bool)
{

  first_anon0:
    first_fnd := elt[first_j] == first_x && valid[first_j];
    goto second_anon0;

  second_anon0:
    elt[second_j] := null;
    owner[second_j] := nil;
    return;
}



procedure CommutativityChecker_atomic_isEltThereAndValid_2_atomic_setEltToNull_2(first_j: int, first_x: int, first_tid: X, second_j: int, second_tid: X)
   returns (first_fnd: bool);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  requires owner[second_j] == second_tid && lock[second_j] == second_tid;
  requires 0 <= second_j && second_j < max;
  requires !valid[second_j];
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> lock == old(lock)
       && elt == old(elt)[second_j := null]
       && valid == old(valid)
       && owner == old(owner)[second_j := nil]
       && (first_fnd
         <==> old(elt)[second_j := null][first_j] == first_x && old(valid)[first_j]);



implementation CommutativityChecker_AtomicFindSlot_2_atomic_setEltToNull_2(first_x: int, first_tid: X, second_j: int, second_tid: X) returns (first_r: int)
{

  first_anon0:
    goto first_anon3_Then, first_anon3_Else;

  first_anon3_Else:
    assume first_r == -1;
    goto second_anon0;

  first_anon3_Then:
    assume 0 <= first_r && first_r < max;
    assume elt[first_r] == null;
    assume owner[first_r] == nil;
    assume !valid[first_r];
    elt[first_r] := first_x;
    owner[first_r] := first_tid;
    goto second_anon0;

  second_anon0:
    elt[second_j] := null;
    owner[second_j] := nil;
    return;
}



procedure CommutativityChecker_AtomicFindSlot_2_atomic_setEltToNull_2(first_x: int, first_tid: X, second_j: int, second_tid: X) returns (first_r: int);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires first_tid != nil && first_tid != done;
  requires first_x != null;
  requires owner[second_j] == second_tid && lock[second_j] == second_tid;
  requires 0 <= second_j && second_j < max;
  requires !valid[second_j];
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> (
        elt == old(elt)[second_j := null][first_r := first_x]
         && owner == old(owner)[second_j := nil][first_r := first_tid]
         && valid == old(valid)
         && lock == old(lock)
         && first_r == first_r
         && !old(valid)[first_r]
         && old(owner)[second_j := nil][first_r] == nil
         && old(elt)[second_j := null][first_r] == null
         && 0 <= first_r
         && first_r < max)
       || (
        elt == old(elt)[second_j := null]
         && owner == old(owner)[second_j := nil]
         && valid == old(valid)
         && lock == old(lock)
         && first_r == first_r
         && first_r == -1);



implementation GatePreservationChecker_atomic_setEltToNull_2_AtomicFindSlot_2(first_j: int, first_tid: X, second_x: int, second_tid: X)
   returns (second_r: int)
{

  second_anon0:
    goto second_anon3_Then, second_anon3_Else;

  second_anon3_Else:
    assume second_r == -1;
    return;

  second_anon3_Then:
    assume 0 <= second_r && second_r < max;
    assume elt[second_r] == null;
    assume owner[second_r] == nil;
    assume !valid[second_r];
    elt[second_r] := second_x;
    owner[second_r] := second_tid;
    return;
}



procedure GatePreservationChecker_atomic_setEltToNull_2_AtomicFindSlot_2(first_j: int, first_tid: X, second_x: int, second_tid: X)
   returns (second_r: int);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires second_tid != nil && second_tid != done;
  requires second_x != null;
  requires owner[first_j] == first_tid && lock[first_j] == first_tid;
  requires 0 <= first_j && first_j < max;
  requires !valid[first_j];
  requires first_tid != nil && first_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> owner[first_j] == first_tid && lock[first_j] == first_tid;
  ensures true ==> 0 <= first_j && first_j < max;
  ensures true ==> !valid[first_j];
  ensures true ==> first_tid != nil && first_tid != done;



implementation GatePreservationChecker_atomic_setValid_2_atomic_release_2(first_j: int, first_tid: X, second_i: int, second_tid: X)
{

  second_anon0:
    lock[second_i] := nil;
    return;
}



procedure GatePreservationChecker_atomic_setValid_2_atomic_release_2(first_j: int, first_tid: X, second_i: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= second_i && second_i < max;
  requires lock[second_i] == second_tid;
  requires second_tid != nil && second_tid != done;
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  requires owner[first_j] == first_tid;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> 0 <= first_j && first_j < max;
  ensures true ==> lock[first_j] == first_tid;
  ensures true ==> first_tid != nil && first_tid != done;
  ensures true ==> owner[first_j] == first_tid;



implementation CommutativityChecker_atomic_setEltToNull_2_atomic_setValid_2(first_j: int, first_tid: X, second_j: int, second_tid: X)
{

  first_anon0:
    elt[first_j] := null;
    owner[first_j] := nil;
    goto second_anon0;

  second_anon0:
    valid[second_j] := true;
    owner[second_j] := done;
    return;
}



procedure CommutativityChecker_atomic_setEltToNull_2_atomic_setValid_2(first_j: int, first_tid: X, second_j: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires owner[first_j] == first_tid && lock[first_j] == first_tid;
  requires 0 <= first_j && first_j < max;
  requires !valid[first_j];
  requires first_tid != nil && first_tid != done;
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  requires owner[second_j] == second_tid;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> owner == old(owner)[second_j := done][first_j := nil]
       && lock == old(lock)
       && valid == old(valid)[second_j := true]
       && elt == old(elt)[first_j := null];



implementation GatePreservationChecker_atomic_setValid_2_atomic_setEltToNull_2(first_j: int, first_tid: X, second_j: int, second_tid: X)
{

  second_anon0:
    elt[second_j] := null;
    owner[second_j] := nil;
    return;
}



procedure GatePreservationChecker_atomic_setValid_2_atomic_setEltToNull_2(first_j: int, first_tid: X, second_j: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires owner[second_j] == second_tid && lock[second_j] == second_tid;
  requires 0 <= second_j && second_j < max;
  requires !valid[second_j];
  requires second_tid != nil && second_tid != done;
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  requires owner[first_j] == first_tid;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> 0 <= first_j && first_j < max;
  ensures true ==> lock[first_j] == first_tid;
  ensures true ==> first_tid != nil && first_tid != done;
  ensures true ==> owner[first_j] == first_tid;



implementation FailurePreservationChecker_atomic_setEltToNull_2_atomic_setValid_2(first_j: int, first_tid: X, second_j: int, second_tid: X)
{

  second_anon0:
    valid[second_j] := true;
    owner[second_j] := done;
    return;
}



procedure FailurePreservationChecker_atomic_setEltToNull_2_atomic_setValid_2(first_j: int, first_tid: X, second_j: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires !(
    owner[first_j] == first_tid
     && lock[first_j] == first_tid
     && 
    0 <= first_j
     && first_j < max
     && !valid[first_j]
     && 
    first_tid != nil
     && first_tid != done);
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  requires owner[second_j] == second_tid;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> !(
      owner[first_j] == first_tid
       && lock[first_j] == first_tid
       && 
      0 <= first_j
       && first_j < max
       && !valid[first_j]
       && 
      first_tid != nil
       && first_tid != done);



implementation CommutativityChecker_atomic_setValid_2_atomic_setValid_2(first_j: int, first_tid: X, second_j: int, second_tid: X)
{

  first_anon0:
    valid[first_j] := true;
    owner[first_j] := done;
    goto second_anon0;

  second_anon0:
    valid[second_j] := true;
    owner[second_j] := done;
    return;
}



procedure CommutativityChecker_atomic_setValid_2_atomic_setValid_2(first_j: int, first_tid: X, second_j: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  requires owner[first_j] == first_tid;
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  requires owner[second_j] == second_tid;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> lock == old(lock)
       && owner == old(owner)[second_j := done][first_j := done]
       && valid == old(valid)[second_j := true][first_j := true];



implementation GatePreservationChecker_atomic_setValid_2_atomic_setValid_2(first_j: int, first_tid: X, second_j: int, second_tid: X)
{

  second_anon0:
    valid[second_j] := true;
    owner[second_j] := done;
    return;
}



procedure GatePreservationChecker_atomic_setValid_2_atomic_setValid_2(first_j: int, first_tid: X, second_j: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  requires owner[second_j] == second_tid;
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  requires owner[first_j] == first_tid;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> 0 <= first_j && first_j < max;
  ensures true ==> lock[first_j] == first_tid;
  ensures true ==> first_tid != nil && first_tid != done;
  ensures true ==> owner[first_j] == first_tid;



implementation FailurePreservationChecker_atomic_setValid_2_atomic_setValid_2(first_j: int, first_tid: X, second_j: int, second_tid: X)
{

  second_anon0:
    valid[second_j] := true;
    owner[second_j] := done;
    return;
}



procedure FailurePreservationChecker_atomic_setValid_2_atomic_setValid_2(first_j: int, first_tid: X, second_j: int, second_tid: X);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires !(
    0 <= first_j
     && first_j < max
     && lock[first_j] == first_tid
     && 
    first_tid != nil
     && first_tid != done
     && owner[first_j] == first_tid);
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  requires owner[second_j] == second_tid;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> !(
      0 <= first_j
       && first_j < max
       && lock[first_j] == first_tid
       && 
      first_tid != nil
       && first_tid != done
       && owner[first_j] == first_tid);



implementation CommutativityChecker_atomic_setValid_2_atomic_isEltThereAndValid_2(first_j: int, first_tid: X, second_j: int, second_x: int, second_tid: X)
   returns (second_fnd: bool)
{

  first_anon0:
    valid[first_j] := true;
    owner[first_j] := done;
    goto second_anon0;

  second_anon0:
    second_fnd := elt[second_j] == second_x && valid[second_j];
    return;
}



procedure CommutativityChecker_atomic_setValid_2_atomic_isEltThereAndValid_2(first_j: int, first_tid: X, second_j: int, second_x: int, second_tid: X)
   returns (second_fnd: bool);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  requires owner[first_j] == first_tid;
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> lock == old(lock)
       && owner == old(owner)[first_j := done]
       && valid == old(valid)[first_j := true]
       && elt == old(elt)
       && (second_fnd <==> old(elt)[second_j] == second_x && old(valid)[second_j]);



implementation CommutativityChecker_atomic_isEltThereAndValid_2_atomic_setValid_2(first_j: int, first_x: int, first_tid: X, second_j: int, second_tid: X)
   returns (first_fnd: bool)
{

  first_anon0:
    first_fnd := elt[first_j] == first_x && valid[first_j];
    goto second_anon0;

  second_anon0:
    valid[second_j] := true;
    owner[second_j] := done;
    return;
}



procedure CommutativityChecker_atomic_isEltThereAndValid_2_atomic_setValid_2(first_j: int, first_x: int, first_tid: X, second_j: int, second_tid: X)
   returns (first_fnd: bool);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  requires owner[second_j] == second_tid;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> lock == old(lock)
       && elt == old(elt)
       && valid == old(valid)[second_j := true]
       && owner == old(owner)[second_j := done]
       && (first_fnd
         <==> old(elt)[first_j] == first_x && old(valid)[second_j := true][first_j]);



implementation CommutativityChecker_atomic_setValid_2_AtomicFindSlot_2(first_j: int, first_tid: X, second_x: int, second_tid: X)
   returns (second_r: int)
{

  first_anon0:
    valid[first_j] := true;
    owner[first_j] := done;
    goto second_anon0;

  second_anon0:
    goto second_anon3_Then, second_anon3_Else;

  second_anon3_Else:
    assume second_r == -1;
    return;

  second_anon3_Then:
    assume 0 <= second_r && second_r < max;
    assume elt[second_r] == null;
    assume owner[second_r] == nil;
    assume !valid[second_r];
    elt[second_r] := second_x;
    owner[second_r] := second_tid;
    return;
}



procedure CommutativityChecker_atomic_setValid_2_AtomicFindSlot_2(first_j: int, first_tid: X, second_x: int, second_tid: X)
   returns (second_r: int);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  requires owner[first_j] == first_tid;
  requires second_tid != nil && second_tid != done;
  requires second_x != null;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> (
        lock == old(lock)
         && owner == old(owner)[second_r := second_tid][first_j := done]
         && valid == old(valid)[first_j := true]
         && elt == old(elt)[second_r := second_x]
         && second_r == second_r
         && !old(valid)[second_r]
         && old(owner)[second_r] == nil
         && old(elt)[second_r] == null
         && 0 <= second_r
         && second_r < max)
       || (
        lock == old(lock)
         && owner == old(owner)[first_j := done]
         && valid == old(valid)[first_j := true]
         && elt == old(elt)
         && second_r == second_r
         && second_r == -1);



implementation CommutativityChecker_AtomicFindSlot_2_atomic_setValid_2(first_x: int, first_tid: X, second_j: int, second_tid: X) returns (first_r: int)
{

  first_anon0:
    goto first_anon3_Then, first_anon3_Else;

  first_anon3_Else:
    assume first_r == -1;
    goto second_anon0;

  first_anon3_Then:
    assume 0 <= first_r && first_r < max;
    assume elt[first_r] == null;
    assume owner[first_r] == nil;
    assume !valid[first_r];
    elt[first_r] := first_x;
    owner[first_r] := first_tid;
    goto second_anon0;

  second_anon0:
    valid[second_j] := true;
    owner[second_j] := done;
    return;
}



procedure CommutativityChecker_AtomicFindSlot_2_atomic_setValid_2(first_x: int, first_tid: X, second_j: int, second_tid: X) returns (first_r: int);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires first_tid != nil && first_tid != done;
  requires first_x != null;
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  requires owner[second_j] == second_tid;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> (
        elt == old(elt)[first_r := first_x]
         && owner == old(owner)[second_j := done][first_r := first_tid]
         && valid == old(valid)[second_j := true]
         && lock == old(lock)
         && first_r == first_r
         && !old(valid)[second_j := true][first_r]
         && old(owner)[second_j := done][first_r] == nil
         && old(elt)[first_r] == null
         && 0 <= first_r
         && first_r < max)
       || (
        elt == old(elt)
         && owner == old(owner)[second_j := done]
         && valid == old(valid)[second_j := true]
         && lock == old(lock)
         && first_r == first_r
         && first_r == -1);



implementation GatePreservationChecker_atomic_setValid_2_AtomicFindSlot_2(first_j: int, first_tid: X, second_x: int, second_tid: X)
   returns (second_r: int)
{

  second_anon0:
    goto second_anon3_Then, second_anon3_Else;

  second_anon3_Else:
    assume second_r == -1;
    return;

  second_anon3_Then:
    assume 0 <= second_r && second_r < max;
    assume elt[second_r] == null;
    assume owner[second_r] == nil;
    assume !valid[second_r];
    elt[second_r] := second_x;
    owner[second_r] := second_tid;
    return;
}



procedure GatePreservationChecker_atomic_setValid_2_AtomicFindSlot_2(first_j: int, first_tid: X, second_x: int, second_tid: X)
   returns (second_r: int);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires second_tid != nil && second_tid != done;
  requires second_x != null;
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  requires owner[first_j] == first_tid;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> 0 <= first_j && first_j < max;
  ensures true ==> lock[first_j] == first_tid;
  ensures true ==> first_tid != nil && first_tid != done;
  ensures true ==> owner[first_j] == first_tid;



implementation GatePreservationChecker_atomic_isEltThereAndValid_2_atomic_release_2(first_j: int, first_x: int, first_tid: X, second_i: int, second_tid: X)
   returns (first_fnd: bool)
{

  second_anon0:
    lock[second_i] := nil;
    return;
}



procedure GatePreservationChecker_atomic_isEltThereAndValid_2_atomic_release_2(first_j: int, first_x: int, first_tid: X, second_i: int, second_tid: X)
   returns (first_fnd: bool);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= second_i && second_i < max;
  requires lock[second_i] == second_tid;
  requires second_tid != nil && second_tid != done;
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true ==> 0 <= first_j && first_j < max;
  ensures true ==> lock[first_j] == first_tid;
  ensures true ==> first_tid != nil && first_tid != done;



implementation CommutativityChecker_atomic_setEltToNull_2_atomic_isEltThereAndValid_2(first_j: int, first_tid: X, second_j: int, second_x: int, second_tid: X)
   returns (second_fnd: bool)
{

  first_anon0:
    elt[first_j] := null;
    owner[first_j] := nil;
    goto second_anon0;

  second_anon0:
    second_fnd := elt[second_j] == second_x && valid[second_j];
    return;
}



procedure CommutativityChecker_atomic_setEltToNull_2_atomic_isEltThereAndValid_2(first_j: int, first_tid: X, second_j: int, second_x: int, second_tid: X)
   returns (second_fnd: bool);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires owner[first_j] == first_tid && lock[first_j] == first_tid;
  requires 0 <= first_j && first_j < max;
  requires !valid[first_j];
  requires first_tid != nil && first_tid != done;
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> owner == old(owner)[first_j := nil]
       && lock == old(lock)
       && valid == old(valid)
       && elt == old(elt)[first_j := null]
       && (second_fnd <==> old(elt)[second_j] == second_x && old(valid)[second_j]);



implementation CommutativityChecker_atomic_isEltThereAndValid_2_AtomicFindSlot_2(first_j: int, first_x: int, first_tid: X, second_x: int, second_tid: X)
   returns (first_fnd: bool, second_r: int)
{

  first_anon0:
    first_fnd := elt[first_j] == first_x && valid[first_j];
    goto second_anon0;

  second_anon0:
    goto second_anon3_Then, second_anon3_Else;

  second_anon3_Else:
    assume second_r == -1;
    return;

  second_anon3_Then:
    assume 0 <= second_r && second_r < max;
    assume elt[second_r] == null;
    assume owner[second_r] == nil;
    assume !valid[second_r];
    elt[second_r] := second_x;
    owner[second_r] := second_tid;
    return;
}



procedure CommutativityChecker_atomic_isEltThereAndValid_2_AtomicFindSlot_2(first_j: int, first_x: int, first_tid: X, second_x: int, second_tid: X)
   returns (first_fnd: bool, second_r: int);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires 0 <= first_j && first_j < max;
  requires lock[first_j] == first_tid;
  requires first_tid != nil && first_tid != done;
  requires second_tid != nil && second_tid != done;
  requires second_x != null;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> (
        lock == old(lock)
         && elt == old(elt)[second_r := second_x]
         && valid == old(valid)
         && owner == old(owner)[second_r := second_tid]
         && (first_fnd
           <==> old(elt)[second_r := second_x][first_j] == first_x && old(valid)[first_j])
         && second_r == second_r
         && !old(valid)[second_r]
         && old(owner)[second_r] == nil
         && old(elt)[second_r] == null
         && 0 <= second_r
         && second_r < max)
       || (
        lock == old(lock)
         && elt == old(elt)
         && valid == old(valid)
         && owner == old(owner)
         && (first_fnd <==> old(elt)[first_j] == first_x && old(valid)[first_j])
         && second_r == second_r
         && second_r == -1);



implementation CommutativityChecker_AtomicFindSlot_2_atomic_isEltThereAndValid_2(first_x: int, first_tid: X, second_j: int, second_x: int, second_tid: X)
   returns (first_r: int, second_fnd: bool)
{

  first_anon0:
    goto first_anon3_Then, first_anon3_Else;

  first_anon3_Else:
    assume first_r == -1;
    goto second_anon0;

  first_anon3_Then:
    assume 0 <= first_r && first_r < max;
    assume elt[first_r] == null;
    assume owner[first_r] == nil;
    assume !valid[first_r];
    elt[first_r] := first_x;
    owner[first_r] := first_tid;
    goto second_anon0;

  second_anon0:
    second_fnd := elt[second_j] == second_x && valid[second_j];
    return;
}



procedure CommutativityChecker_AtomicFindSlot_2_atomic_isEltThereAndValid_2(first_x: int, first_tid: X, second_j: int, second_x: int, second_tid: X)
   returns (first_r: int, second_fnd: bool);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires first_tid != nil && first_tid != done;
  requires first_x != null;
  requires 0 <= second_j && second_j < max;
  requires lock[second_j] == second_tid;
  requires second_tid != nil && second_tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> (
        elt == old(elt)[first_r := first_x]
         && owner == old(owner)[first_r := first_tid]
         && valid == old(valid)
         && lock == old(lock)
         && first_r == first_r
         && (second_fnd <==> old(elt)[second_j] == second_x && old(valid)[second_j])
         && !old(valid)[first_r]
         && old(owner)[first_r] == nil
         && old(elt)[first_r] == null
         && 0 <= first_r
         && first_r < max)
       || (
        elt == old(elt)
         && owner == old(owner)
         && valid == old(valid)
         && lock == old(lock)
         && first_r == first_r
         && (second_fnd <==> old(elt)[second_j] == second_x && old(valid)[second_j])
         && first_r == -1);



implementation CommutativityChecker_AtomicFindSlot_2_AtomicFindSlot_2(first_x: int, first_tid: X, second_x: int, second_tid: X)
   returns (first_r: int, second_r: int)
{

  first_anon0:
    goto first_anon3_Then, first_anon3_Else;

  first_anon3_Else:
    assume first_r == -1;
    goto second_anon0;

  first_anon3_Then:
    assume 0 <= first_r && first_r < max;
    assume elt[first_r] == null;
    assume owner[first_r] == nil;
    assume !valid[first_r];
    elt[first_r] := first_x;
    owner[first_r] := first_tid;
    goto second_anon0;

  second_anon0:
    goto second_anon3_Then, second_anon3_Else;

  second_anon3_Else:
    assume second_r == -1;
    return;

  second_anon3_Then:
    assume 0 <= second_r && second_r < max;
    assume elt[second_r] == null;
    assume owner[second_r] == nil;
    assume !valid[second_r];
    elt[second_r] := second_x;
    owner[second_r] := second_tid;
    return;
}



procedure CommutativityChecker_AtomicFindSlot_2_AtomicFindSlot_2(first_x: int, first_tid: X, second_x: int, second_tid: X)
   returns (first_r: int, second_r: int);
  requires (exists partition_tid: [X]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires first_tid != nil && first_tid != done;
  requires first_x != null;
  requires second_tid != nil && second_tid != done;
  requires second_x != null;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures true
     ==> (
        elt == old(elt)[second_r := second_x][first_r := first_x]
         && owner == old(owner)[second_r := second_tid][first_r := first_tid]
         && valid == old(valid)
         && first_r == first_r
         && second_r == second_r
         && !old(valid)[first_r]
         && old(owner)[second_r := second_tid][first_r] == nil
         && old(elt)[second_r := second_x][first_r] == null
         && 0 <= first_r
         && first_r < max
         && !old(valid)[second_r]
         && old(owner)[second_r] == nil
         && old(elt)[second_r] == null
         && 0 <= second_r
         && second_r < max)
       || (
        elt == old(elt)[second_r := second_x]
         && owner == old(owner)[second_r := second_tid]
         && valid == old(valid)
         && first_r == first_r
         && second_r == second_r
         && first_r == -1
         && !old(valid)[second_r]
         && old(owner)[second_r] == nil
         && old(elt)[second_r] == null
         && 0 <= second_r
         && second_r < max)
       || (
        elt == old(elt)[first_r := first_x]
         && owner == old(owner)[first_r := first_tid]
         && valid == old(valid)
         && first_r == first_r
         && second_r == second_r
         && !old(valid)[first_r]
         && old(owner)[first_r] == nil
         && old(elt)[first_r] == null
         && 0 <= first_r
         && first_r < max
         && second_r == -1)
       || (
        elt == old(elt)
         && owner == old(owner)
         && valid == old(valid)
         && first_r == first_r
         && second_r == second_r
         && first_r == -1
         && second_r == -1);



procedure {:inline 1} skip_dummy_Yield1();



implementation {:inline 1} skip_dummy_Yield1()
{

  _init:
    return;
}



procedure {:inline 1} skip_dummy_Yield12();



implementation {:inline 1} skip_dummy_Yield12()
{

  _init:
    return;
}



procedure {:inline 1} skip_dummy_YieldLookUp(old_valid: [int]bool, old_elt: [int]int);



implementation {:inline 1} skip_dummy_YieldLookUp(old_valid: [int]bool, old_elt: [int]int)
{

  _init:
    return;
}



procedure acquire_0(i: int, tid: X);
  modifies elt, valid, lock, owner, pendingAsyncMultiset;



procedure release_0(i: int, tid: X);
  modifies elt, valid, lock, owner, pendingAsyncMultiset;



procedure getElt_0(j: int, tid: X) returns (elt_j: int);
  modifies elt, valid, lock, owner, pendingAsyncMultiset;



procedure setElt_0(j: int, x: int, tid: X);
  modifies elt, valid, lock, owner, pendingAsyncMultiset;



procedure setEltToNull_0(j: int, tid: X);
  modifies elt, valid, lock, owner, pendingAsyncMultiset;



procedure setValid_0(j: int, tid: X);
  modifies elt, valid, lock, owner, pendingAsyncMultiset;



procedure isEltThereAndValid_0(j: int, x: int, tid: X) returns (fnd: bool);
  modifies elt, valid, lock, owner, pendingAsyncMultiset;



procedure FindSlot_0(x: int, tid: X) returns (r: int);
  modifies elt, valid, lock, owner, pendingAsyncMultiset;



procedure Insert_0(x: int, tid: X) returns (result: bool);
  modifies elt, valid, lock, owner, pendingAsyncMultiset;



procedure InsertPair_0(x: int, y: int, tid: X) returns (result: bool);
  modifies elt, valid, lock, owner, pendingAsyncMultiset;



procedure LookUp_0(x: int, tid: X, old_valid: [int]bool, old_elt: [int]int) returns (found: bool);
  modifies elt, valid, lock, owner, pendingAsyncMultiset;



procedure Yield1_0();
  modifies elt, valid, lock, owner, pendingAsyncMultiset;



procedure Yield12_0();
  modifies elt, valid, lock, owner, pendingAsyncMultiset;



procedure YieldLookUp_0(old_valid: [int]bool, old_elt: [int]int);
  modifies elt, valid, lock, owner, pendingAsyncMultiset;



implementation FindSlot_0(x: int, tid: X) returns (r: int)
{
  var j: int;
  var elt_j: int;
  var og_global_old_elt: [int]int;
  var og_global_old_valid: [int]bool;
  var og_global_old_lock: [int]X;
  var og_global_old_owner: [int]X;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_tid_available: [X]bool;

  /*** structured program:
    j := 0;
    while (j < max)
      invariant Inv(valid, elt, owner);
      invariant 0 <= j;
    {
        call acquire(j, tid);
        call elt_j := getElt(j, tid);
        if (elt_j == null)
        {
            call setElt(j, x, tid);
            call release(j, tid);
            r := j;
            return;
        }

        call release(j, tid);
        j := j + 1;
    }

    r := -1;
    return;
  **** end structured program */

  og_init:
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon5_LoopHead:
    assume linear_tid_available
       == linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false));
    assume elt == og_global_old_elt;
    assume valid == og_global_old_valid;
    assume lock == og_global_old_lock;
    assume owner == og_global_old_owner;
    assume pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon5_LoopDone, anon5_LoopBody;

  anon5_LoopBody:
    assume {:partition} j < max;
    goto anon5_LoopBody1, CallToYieldProc;

  anon6_Else:
    assume {:partition} elt_j != null;
    goto anon3;

  anon3:
    goto anon30, CallToYieldProc;

  anon6_Then:
    assume {:partition} elt_j == null;
    goto anon6_Then1, CallToYieldProc;

  anon5_LoopDone:
    assume {:partition} max <= j;
    goto anon4;

  anon4:
    r := -1;
    goto anon41, CallToYieldProc;

  anon05:
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    goto anon5_LoopHead;

  anon00:
    call og_Yield1_0();
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    j := 0;
    goto anon05, CallToYieldProc;

  anon5_LoopBody5:
    call elt_j := getElt_0(j, tid);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon6_Then, anon6_Else;

  anon5_LoopBody1:
    call acquire_0(j, tid);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon5_LoopBody5, CallToYieldProc;

  anon39:
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    goto anon5_LoopHead;

  anon34:
    call og_Yield1_0();
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    j := j + 1;
    goto anon39, CallToYieldProc;

  anon30:
    call release_0(j, tid);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon34, CallToYieldProc;

  anon6_Then14:
    return;

  anon6_Then10:
    call og_Yield1_0();
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon6_Then14, CallToYieldProc;

  anon6_Then5:
    call release_0(j, tid);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    r := j;
    goto anon6_Then10, CallToYieldProc;

  anon6_Then1:
    call setElt_0(j, x, tid);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon6_Then5, CallToYieldProc;

  anon45:
    return;

  anon41:
    call og_Yield1_0();
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon45, CallToYieldProc;

  CallToYieldProc:
    call og_yield_0(linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation Insert_0(x: int, tid: X) returns (result: bool)
{
  var i: int;
  var og_global_old_elt: [int]int;
  var og_global_old_valid: [int]bool;
  var og_global_old_lock: [int]X;
  var og_global_old_owner: [int]X;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_tid_available: [X]bool;

  /*** structured program:
    call i := FindSlot(x, tid);
    if (i == -1)
    {
        result := false;
        return;
    }

    assert i != -1;
    assert i != -1;
    call acquire(i, tid);
    assert elt[i] == x;
    assert valid[i] <==> false;
    call setValid(i, tid);
    call release(i, tid);
    result := true;
    return;
  **** end structured program */

  og_init:
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon3_Else:
    assume {:partition} i != -1;
    goto anon2;

  anon2:
    goto anon20, CallToYieldProc;

  anon3_Then:
    assume {:partition} i == -1;
    result := false;
    goto anon3_Then2, CallToYieldProc;

  anon04:
    call i := FindSlot_0(x, tid);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon3_Then, anon3_Else;

  anon00:
    call og_Yield12_0();
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon04, CallToYieldProc;

  anon221:
    return;

  anon217:
    call og_Yield12_0();
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon221, CallToYieldProc;

  anon212:
    call release_0(i, tid);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    result := true;
    goto anon217, CallToYieldProc;

  anon28:
    call setValid_0(i, tid);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon212, CallToYieldProc;

  anon24:
    call acquire_0(i, tid);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon28, CallToYieldProc;

  anon20:
    call og_Yield1_0();
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon24, CallToYieldProc;

  anon3_Then6:
    return;

  anon3_Then2:
    call og_Yield12_0();
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon3_Then6, CallToYieldProc;

  CallToYieldProc:
    call og_yield_0(linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation InsertPair_0(x: int, y: int, tid: X) returns (result: bool)
{
  var i: int;
  var j: int;
  var og_global_old_elt: [int]int;
  var og_global_old_valid: [int]bool;
  var og_global_old_lock: [int]X;
  var og_global_old_owner: [int]X;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_tid_available: [X]bool;

  /*** structured program:
    call i := FindSlot(x, tid);
    if (i == -1)
    {
        result := false;
        return;
    }

    call j := FindSlot(y, tid);
    if (j == -1)
    {
        call acquire(i, tid);
        call setEltToNull(i, tid);
        call release(i, tid);
        result := false;
        return;
    }

    assert i != -1 && j != -1;
    call acquire(i, tid);
    call acquire(j, tid);
    assert elt[i] == x;
    assert elt[j] == y;
    assert valid[i] <==> false;
    assert valid[j] <==> false;
    call setValid(i, tid);
    call setValid(j, tid);
    call release(j, tid);
    call release(i, tid);
    result := true;
    return;
  **** end structured program */

  og_init:
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon5_Else:
    assume {:partition} i != -1;
    goto anon2;

  anon2:
    goto anon20, CallToYieldProc;

  anon6_Else:
    assume {:partition} j != -1;
    goto anon4;

  anon4:
    goto anon40, CallToYieldProc;

  anon6_Then:
    assume {:partition} j == -1;
    goto anon6_Then1, CallToYieldProc;

  anon5_Then:
    assume {:partition} i == -1;
    result := false;
    goto anon5_Then2, CallToYieldProc;

  anon04:
    call i := FindSlot_0(x, tid);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon5_Then, anon5_Else;

  anon00:
    call og_Yield12_0();
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon04, CallToYieldProc;

  anon24:
    call j := FindSlot_0(y, tid);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon6_Then, anon6_Else;

  anon20:
    call og_Yield1_0();
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon24, CallToYieldProc;

  anon433:
    return;

  anon429:
    call og_Yield12_0();
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon433, CallToYieldProc;

  anon424:
    call release_0(i, tid);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    result := true;
    goto anon429, CallToYieldProc;

  anon420:
    call release_0(j, tid);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon424, CallToYieldProc;

  anon416:
    call setValid_0(j, tid);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon420, CallToYieldProc;

  anon412:
    call setValid_0(i, tid);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon416, CallToYieldProc;

  anon48:
    call acquire_0(j, tid);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon412, CallToYieldProc;

  anon44:
    call acquire_0(i, tid);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon48, CallToYieldProc;

  anon40:
    call og_Yield1_0();
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon44, CallToYieldProc;

  anon6_Then22:
    return;

  anon6_Then18:
    call og_Yield12_0();
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon6_Then22, CallToYieldProc;

  anon6_Then13:
    call release_0(i, tid);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    result := false;
    goto anon6_Then18, CallToYieldProc;

  anon6_Then9:
    call setEltToNull_0(i, tid);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon6_Then13, CallToYieldProc;

  anon6_Then5:
    call acquire_0(i, tid);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon6_Then9, CallToYieldProc;

  anon6_Then1:
    call og_Yield1_0();
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon6_Then5, CallToYieldProc;

  anon5_Then6:
    return;

  anon5_Then2:
    call og_Yield12_0();
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon5_Then6, CallToYieldProc;

  CallToYieldProc:
    call og_yield_0(linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation LookUp_0(x: int, tid: X, old_valid: [int]bool, old_elt: [int]int) returns (found: bool)
{
  var j: int;
  var isThere: bool;
  var og_global_old_elt: [int]int;
  var og_global_old_valid: [int]bool;
  var og_global_old_lock: [int]X;
  var og_global_old_owner: [int]X;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_tid_available: [X]bool;

  /*** structured program:
    j := 0;
    while (j < max)
      invariant Inv(valid, elt, owner);
      invariant (forall ii: int :: 0 <= ii && ii < j ==> !(old_valid[ii] && old_elt[ii] == x));
      invariant (forall ii: int :: 
        0 <= ii && ii < max && old_valid[ii] ==> valid[ii] && old_elt[ii] == elt[ii]);
      invariant 0 <= j;
    {
        call acquire(j, tid);
        call isThere := isEltThereAndValid(j, x, tid);
        if (isThere)
        {
            call release(j, tid);
            found := true;
            return;
        }

        call release(j, tid);
        j := j + 1;
    }

    found := false;
    return;
  **** end structured program */

  og_init:
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon5_LoopHead:
    assume linear_tid_available
       == linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false));
    assume elt == og_global_old_elt;
    assume valid == og_global_old_valid;
    assume lock == og_global_old_lock;
    assume owner == og_global_old_owner;
    assume pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon5_LoopDone, anon5_LoopBody;

  anon5_LoopBody:
    assume {:partition} j < max;
    goto anon5_LoopBody1, CallToYieldProc;

  anon6_Else:
    assume {:partition} !isThere;
    goto anon3;

  anon3:
    goto anon30, CallToYieldProc;

  anon6_Then:
    assume {:partition} isThere;
    goto anon6_Then1, CallToYieldProc;

  anon5_LoopDone:
    assume {:partition} max <= j;
    goto anon4;

  anon4:
    found := false;
    goto anon41, CallToYieldProc;

  anon05:
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    goto anon5_LoopHead;

  anon00:
    call og_Yield12_0_YieldLookUp_0(old_valid, old_elt);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    j := 0;
    goto anon05, CallToYieldProc;

  anon5_LoopBody5:
    call isThere := isEltThereAndValid_0(j, x, tid);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon6_Then, anon6_Else;

  anon5_LoopBody1:
    call acquire_0(j, tid);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon5_LoopBody5, CallToYieldProc;

  anon39:
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    goto anon5_LoopHead;

  anon34:
    call og_Yield12_0_YieldLookUp_0(old_valid, old_elt);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    j := j + 1;
    goto anon39, CallToYieldProc;

  anon30:
    call release_0(j, tid);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon34, CallToYieldProc;

  anon6_Then10:
    return;

  anon6_Then6:
    call og_Yield12_0_YieldLookUp_0(old_valid, old_elt);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon6_Then10, CallToYieldProc;

  anon6_Then1:
    call release_0(j, tid);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    found := true;
    goto anon6_Then6, CallToYieldProc;

  anon45:
    return;

  anon41:
    call og_Yield12_0_YieldLookUp_0(old_valid, old_elt);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon45, CallToYieldProc;

  CallToYieldProc:
    call og_yield_0(linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation Yield1_0()
{
  var og_global_old_elt: [int]int;
  var og_global_old_valid: [int]bool;
  var og_global_old_lock: [int]X;
  var og_global_old_owner: [int]X;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_tid_available: [X]bool;

  /*** structured program:
    yield;
    assert Inv(valid, elt, owner);
  **** end structured program */

  og_init:
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapConstBool(false), elt, valid, lock, owner, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon03:
    return;

  anon00:
    havoc elt, valid, lock, owner, pendingAsyncMultiset;
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapConstBool(false), elt, valid, lock, owner, pendingAsyncMultiset;
    goto anon03, CallToYieldProc;

  CallToYieldProc:
    call og_yield_0(linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation Yield12_0()
{
  var og_global_old_elt: [int]int;
  var og_global_old_valid: [int]bool;
  var og_global_old_lock: [int]X;
  var og_global_old_owner: [int]X;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_tid_available: [X]bool;

  /*** structured program:
    yield;
    assert Inv(valid, elt, owner);
  **** end structured program */

  og_init:
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapConstBool(false), elt, valid, lock, owner, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon03:
    return;

  anon00:
    havoc elt, valid, lock, owner, pendingAsyncMultiset;
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapConstBool(false), elt, valid, lock, owner, pendingAsyncMultiset;
    goto anon03, CallToYieldProc;

  CallToYieldProc:
    call og_yield_0(linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation YieldLookUp_0(old_valid: [int]bool, old_elt: [int]int)
{
  var og_global_old_elt: [int]int;
  var og_global_old_valid: [int]bool;
  var og_global_old_lock: [int]X;
  var og_global_old_owner: [int]X;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_tid_available: [X]bool;

  /*** structured program:
    yield;
    assert (forall ii: int :: 
      0 <= ii && ii < max && old_valid[ii] ==> valid[ii] && old_elt[ii] == elt[ii]);
  **** end structured program */

  og_init:
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapConstBool(false), elt, valid, lock, owner, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon03:
    return;

  anon00:
    havoc elt, valid, lock, owner, pendingAsyncMultiset;
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapConstBool(false), elt, valid, lock, owner, pendingAsyncMultiset;
    goto anon03, CallToYieldProc;

  CallToYieldProc:
    call og_yield_0(linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



procedure og_Yield1_0();
  modifies elt, valid, lock, owner, pendingAsyncMultiset;



procedure og_Yield12_0();
  modifies elt, valid, lock, owner, pendingAsyncMultiset;



procedure og_Yield12_0_YieldLookUp_0(og_1_old_valid: [int]bool, og_1_old_elt: [int]int);
  modifies elt, valid, lock, owner, pendingAsyncMultiset;



procedure {:inline 1} og_yield_0(linear_tid_in: [X]bool, 
    og_global_old_elt: [int]int, 
    og_global_old_valid: [int]bool, 
    og_global_old_lock: [int]X, 
    og_global_old_owner: [int]X, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



implementation {:inline 1} og_yield_0(linear_tid_in: [X]bool, 
    og_global_old_elt: [int]int, 
    og_global_old_valid: [int]bool, 
    og_global_old_lock: [int]X, 
    og_global_old_owner: [int]X, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{

  enter:
    return;
}



procedure FindSlot_1(x: int, tid: X) returns (r: int);
  requires Inv(valid, elt, owner) && x != null && tid != nil && tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures Inv(valid, elt, owner);



procedure Insert_1(x: int, tid: X) returns (result: bool);
  requires Inv(valid, elt, owner) && x != null && tid != nil && tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures Inv(valid, elt, owner);



procedure InsertPair_1(x: int, y: int, tid: X) returns (result: bool);
  requires Inv(valid, elt, owner) && x != null && y != null && tid != nil && tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures Inv(valid, elt, owner);



procedure LookUp_1(x: int, tid: X, old_valid: [int]bool, old_elt: [int]int) returns (found: bool);
  requires old_valid == valid && old_elt == elt;
  requires Inv(valid, elt, owner);
  requires tid != nil && tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures Inv(valid, elt, owner);



procedure Yield1_1();
  requires Inv(valid, elt, owner);
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures Inv(valid, elt, owner);



procedure Yield12_1();
  requires Inv(valid, elt, owner);
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures Inv(valid, elt, owner);



procedure YieldLookUp_1(old_valid: [int]bool, old_elt: [int]int);
  requires (forall ii: int :: 
    0 <= ii && ii < max && old_valid[ii] ==> valid[ii] && old_elt[ii] == elt[ii]);
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures (forall ii: int :: 
    0 <= ii && ii < max && old_valid[ii] ==> valid[ii] && old_elt[ii] == elt[ii]);



implementation FindSlot_1(x: int, tid: X) returns (r: int)
{
  var j: int;
  var elt_j: int;
  var og_global_old_elt: [int]int;
  var og_global_old_valid: [int]bool;
  var og_global_old_lock: [int]X;
  var og_global_old_owner: [int]X;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;
  var og_old_r: int;
  var linear_tid_available: [X]bool;
  var og_pc_anon5_LoopHead: bool;
  var og_ok_anon5_LoopHead: bool;

  /*** structured program:
    j := 0;
    while (j < max)
      invariant Inv(valid, elt, owner);
      invariant 0 <= j;
    {
        call acquire(j, tid);
        call elt_j := getElt(j, tid);
        if (elt_j == null)
        {
            call setElt(j, x, tid);
            call release(j, tid);
            r := j;
            return;
        }

        call release(j, tid);
        j := j + 1;
    }

    r := -1;
    return;
  **** end structured program */

  og_init:
    og_pc, og_pc_anon5_LoopHead, og_ok, og_ok_anon5_LoopHead, linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset, og_old_r := false, false, false, false, linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset, r;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon5_LoopHead:
    assert og_pc_anon5_LoopHead == og_pc;
    assert og_ok_anon5_LoopHead ==> og_ok;
    assume linear_tid_available
       == linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false));
    assume elt == og_global_old_elt;
    assume valid == og_global_old_valid;
    assume lock == og_global_old_lock;
    assume owner == og_global_old_owner;
    assume pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assume r == og_old_r;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assert Inv(valid, elt, owner);
    assert 0 <= j;
    goto anon5_LoopDone, anon5_LoopBody;

  anon5_LoopBody:
    assume {:partition} j < max;
    // <<< injected gate
    assert 0 <= j && j < max;
    assert tid != nil && tid != done;
    // injected gate >>>
    call atomic_acquire_1(j, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    // <<< injected gate
    assert 0 <= j && j < max;
    assert tid != nil && tid != done;
    assert lock[j] == tid;
    // injected gate >>>
    call elt_j := atomic_getElt_1(j, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon6_Then, anon6_Else;

  anon6_Else:
    assume {:partition} elt_j != null;
    goto anon3;

  anon3:
    // <<< injected gate
    assert 0 <= j && j < max;
    assert lock[j] == tid;
    assert tid != nil && tid != done;
    // injected gate >>>
    call atomic_release_1(j, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon37, CallToYieldProc;

  anon6_Then:
    assume {:partition} elt_j == null;
    // <<< injected gate
    assert x != null && owner[j] == nil;
    assert 0 <= j && j < max;
    assert lock[j] == tid;
    assert tid != nil && tid != done;
    // injected gate >>>
    call atomic_setElt_1(j, x, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    // <<< injected gate
    assert 0 <= j && j < max;
    assert lock[j] == tid;
    assert tid != nil && tid != done;
    // injected gate >>>
    call atomic_release_1(j, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    r := j;
    goto anon6_Then17, CallToYieldProc;

  anon5_LoopDone:
    assume {:partition} max <= j;
    goto anon4;

  anon4:
    r := -1;
    goto anon41, CallToYieldProc;

  anon09:
    assert og_pc
       || 
      (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (
        elt == og_global_old_elt[r := x]
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner[r := tid]
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == r
         && !og_global_old_valid[r]
         && og_global_old_owner[r] == nil
         && og_global_old_elt[r] == null
         && 0 <= r
         && r < max)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == r
         && r == -1);
    assert og_pc
       ==> elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == og_old_r;
    og_pc, og_ok := elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (
        elt == og_global_old_elt[r := x]
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner[r := tid]
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == r
         && !og_global_old_valid[r]
         && og_global_old_owner[r] == nil
         && og_global_old_elt[r] == null
         && 0 <= r
         && r < max)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == r
         && r == -1);
    og_pc_anon5_LoopHead, og_ok_anon5_LoopHead := og_pc, og_ok;
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset, og_old_r := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset, r;
    goto anon5_LoopHead;

  anon00:
    assert og_pc
       || 
      (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (
        elt == og_global_old_elt[r := x]
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner[r := tid]
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == r
         && !og_global_old_valid[r]
         && og_global_old_owner[r] == nil
         && og_global_old_elt[r] == null
         && 0 <= r
         && r < max)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == r
         && r == -1);
    assert og_pc
       ==> elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == og_old_r;
    og_pc, og_ok := elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (
        elt == og_global_old_elt[r := x]
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner[r := tid]
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == r
         && !og_global_old_valid[r]
         && og_global_old_owner[r] == nil
         && og_global_old_elt[r] == null
         && 0 <= r
         && r < max)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == r
         && r == -1);
    call og_Yield1_1();
    assume og_pc || (tid != nil && tid != done && x != null);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset, og_old_r := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset, r;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    j := 0;
    goto anon09, CallToYieldProc;

  anon316:
    assert og_pc
       || 
      (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (
        elt == og_global_old_elt[r := x]
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner[r := tid]
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == r
         && !og_global_old_valid[r]
         && og_global_old_owner[r] == nil
         && og_global_old_elt[r] == null
         && 0 <= r
         && r < max)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == r
         && r == -1);
    assert og_pc
       ==> elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == og_old_r;
    og_pc, og_ok := elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (
        elt == og_global_old_elt[r := x]
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner[r := tid]
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == r
         && !og_global_old_valid[r]
         && og_global_old_owner[r] == nil
         && og_global_old_elt[r] == null
         && 0 <= r
         && r < max)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == r
         && r == -1);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset, og_old_r := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset, r;
    goto anon5_LoopHead;

  anon37:
    assert og_pc
       || 
      (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (
        elt == og_global_old_elt[r := x]
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner[r := tid]
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == r
         && !og_global_old_valid[r]
         && og_global_old_owner[r] == nil
         && og_global_old_elt[r] == null
         && 0 <= r
         && r < max)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == r
         && r == -1);
    assert og_pc
       ==> elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == og_old_r;
    og_pc, og_ok := elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (
        elt == og_global_old_elt[r := x]
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner[r := tid]
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == r
         && !og_global_old_valid[r]
         && og_global_old_owner[r] == nil
         && og_global_old_elt[r] == null
         && 0 <= r
         && r < max)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == r
         && r == -1);
    call og_Yield1_1();
    assume og_pc || (tid != nil && tid != done && x != null);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset, og_old_r := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset, r;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    j := j + 1;
    goto anon316, CallToYieldProc;

  anon6_Then25:
    assert og_pc
       || 
      (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (
        elt == og_global_old_elt[r := x]
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner[r := tid]
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == r
         && !og_global_old_valid[r]
         && og_global_old_owner[r] == nil
         && og_global_old_elt[r] == null
         && 0 <= r
         && r < max)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == r
         && r == -1);
    assert og_pc
       ==> elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == og_old_r;
    og_pc, og_ok := elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (
        elt == og_global_old_elt[r := x]
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner[r := tid]
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == r
         && !og_global_old_valid[r]
         && og_global_old_owner[r] == nil
         && og_global_old_elt[r] == null
         && 0 <= r
         && r < max)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == r
         && r == -1);
    assert og_ok;
    return;

  anon6_Then17:
    assert og_pc
       || 
      (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (
        elt == og_global_old_elt[r := x]
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner[r := tid]
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == r
         && !og_global_old_valid[r]
         && og_global_old_owner[r] == nil
         && og_global_old_elt[r] == null
         && 0 <= r
         && r < max)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == r
         && r == -1);
    assert og_pc
       ==> elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == og_old_r;
    og_pc, og_ok := elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (
        elt == og_global_old_elt[r := x]
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner[r := tid]
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == r
         && !og_global_old_valid[r]
         && og_global_old_owner[r] == nil
         && og_global_old_elt[r] == null
         && 0 <= r
         && r < max)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == r
         && r == -1);
    call og_Yield1_1();
    assume og_pc || (tid != nil && tid != done && x != null);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset, og_old_r := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset, r;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon6_Then25, CallToYieldProc;

  anon49:
    assert og_pc
       || 
      (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (
        elt == og_global_old_elt[r := x]
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner[r := tid]
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == r
         && !og_global_old_valid[r]
         && og_global_old_owner[r] == nil
         && og_global_old_elt[r] == null
         && 0 <= r
         && r < max)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == r
         && r == -1);
    assert og_pc
       ==> elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == og_old_r;
    og_pc, og_ok := elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (
        elt == og_global_old_elt[r := x]
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner[r := tid]
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == r
         && !og_global_old_valid[r]
         && og_global_old_owner[r] == nil
         && og_global_old_elt[r] == null
         && 0 <= r
         && r < max)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == r
         && r == -1);
    assert og_ok;
    return;

  anon41:
    assert og_pc
       || 
      (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (
        elt == og_global_old_elt[r := x]
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner[r := tid]
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == r
         && !og_global_old_valid[r]
         && og_global_old_owner[r] == nil
         && og_global_old_elt[r] == null
         && 0 <= r
         && r < max)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == r
         && r == -1);
    assert og_pc
       ==> elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == og_old_r;
    og_pc, og_ok := elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (
        elt == og_global_old_elt[r := x]
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner[r := tid]
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == r
         && !og_global_old_valid[r]
         && og_global_old_owner[r] == nil
         && og_global_old_elt[r] == null
         && 0 <= r
         && r < max)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && r == r
         && r == -1);
    call og_Yield1_1();
    assume og_pc || (tid != nil && tid != done && x != null);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset, og_old_r := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset, r;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon49, CallToYieldProc;

  CallToYieldProc:
    call og_yield_1(linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation Insert_1(x: int, tid: X) returns (result: bool)
{
  var i: int;
  var og_global_old_elt: [int]int;
  var og_global_old_valid: [int]bool;
  var og_global_old_lock: [int]X;
  var og_global_old_owner: [int]X;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_tid_available: [X]bool;

  /*** structured program:
    call i := FindSlot(x, tid);
    if (i == -1)
    {
        result := false;
        return;
    }

    assert i != -1;
    assert i != -1;
    call acquire(i, tid);
    assert elt[i] == x;
    assert valid[i] <==> false;
    call setValid(i, tid);
    call release(i, tid);
    result := true;
    return;
  **** end structured program */

  og_init:
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon3_Else:
    assume {:partition} i != -1;
    goto anon2;

  anon2:
    goto anon20, CallToYieldProc;

  anon3_Then:
    assume {:partition} i == -1;
    result := false;
    goto anon3_Then2, CallToYieldProc;

  anon04:
    call i := FindSlot_1(x, tid);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon3_Then, anon3_Else;

  anon00:
    call og_Yield12_1();
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon04, CallToYieldProc;

  anon231:
    return;

  anon227:
    call og_Yield12_1();
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon231, CallToYieldProc;

  anon20:
    call og_Yield1_1();
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assert i != -1;
    // <<< injected gate
    assume 0 <= i && i < max;
    assume tid != nil && tid != done;
    // injected gate >>>
    call atomic_acquire_1(i, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    // <<< injected gate
    assume 0 <= i && i < max;
    assume lock[i] == tid;
    assume tid != nil && tid != done;
    assume owner[i] == tid;
    // injected gate >>>
    call atomic_setValid_1(i, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    // <<< injected gate
    assume 0 <= i && i < max;
    assume lock[i] == tid;
    assume tid != nil && tid != done;
    // injected gate >>>
    call atomic_release_1(i, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    result := true;
    goto anon227, CallToYieldProc;

  anon3_Then6:
    return;

  anon3_Then2:
    call og_Yield12_1();
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon3_Then6, CallToYieldProc;

  CallToYieldProc:
    call og_yield_1(linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation InsertPair_1(x: int, y: int, tid: X) returns (result: bool)
{
  var i: int;
  var j: int;
  var og_global_old_elt: [int]int;
  var og_global_old_valid: [int]bool;
  var og_global_old_lock: [int]X;
  var og_global_old_owner: [int]X;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_tid_available: [X]bool;

  /*** structured program:
    call i := FindSlot(x, tid);
    if (i == -1)
    {
        result := false;
        return;
    }

    call j := FindSlot(y, tid);
    if (j == -1)
    {
        call acquire(i, tid);
        call setEltToNull(i, tid);
        call release(i, tid);
        result := false;
        return;
    }

    assert i != -1 && j != -1;
    call acquire(i, tid);
    call acquire(j, tid);
    assert elt[i] == x;
    assert elt[j] == y;
    assert valid[i] <==> false;
    assert valid[j] <==> false;
    call setValid(i, tid);
    call setValid(j, tid);
    call release(j, tid);
    call release(i, tid);
    result := true;
    return;
  **** end structured program */

  og_init:
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon5_Else:
    assume {:partition} i != -1;
    goto anon2;

  anon2:
    goto anon20, CallToYieldProc;

  anon6_Else:
    assume {:partition} j != -1;
    goto anon4;

  anon4:
    goto anon40, CallToYieldProc;

  anon6_Then:
    assume {:partition} j == -1;
    goto anon6_Then1, CallToYieldProc;

  anon5_Then:
    assume {:partition} i == -1;
    result := false;
    goto anon5_Then2, CallToYieldProc;

  anon04:
    call i := FindSlot_1(x, tid);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon5_Then, anon5_Else;

  anon00:
    call og_Yield12_1();
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon04, CallToYieldProc;

  anon24:
    call j := FindSlot_1(y, tid);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon6_Then, anon6_Else;

  anon20:
    call og_Yield1_1();
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon24, CallToYieldProc;

  anon451:
    return;

  anon447:
    call og_Yield12_1();
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon451, CallToYieldProc;

  anon40:
    call og_Yield1_1();
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    // <<< injected gate
    assume 0 <= i && i < max;
    assume tid != nil && tid != done;
    // injected gate >>>
    call atomic_acquire_1(i, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    // <<< injected gate
    assume 0 <= j && j < max;
    assume tid != nil && tid != done;
    // injected gate >>>
    call atomic_acquire_1(j, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    // <<< injected gate
    assume 0 <= i && i < max;
    assume lock[i] == tid;
    assume tid != nil && tid != done;
    assume owner[i] == tid;
    // injected gate >>>
    call atomic_setValid_1(i, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    // <<< injected gate
    assume 0 <= j && j < max;
    assume lock[j] == tid;
    assume tid != nil && tid != done;
    assume owner[j] == tid;
    // injected gate >>>
    call atomic_setValid_1(j, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    // <<< injected gate
    assume 0 <= j && j < max;
    assume lock[j] == tid;
    assume tid != nil && tid != done;
    // injected gate >>>
    call atomic_release_1(j, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    // <<< injected gate
    assume 0 <= i && i < max;
    assume lock[i] == tid;
    assume tid != nil && tid != done;
    // injected gate >>>
    call atomic_release_1(i, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    result := true;
    goto anon447, CallToYieldProc;

  anon6_Then31:
    return;

  anon6_Then27:
    call og_Yield12_1();
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon6_Then31, CallToYieldProc;

  anon6_Then1:
    call og_Yield1_1();
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    // <<< injected gate
    assume 0 <= i && i < max;
    assume tid != nil && tid != done;
    // injected gate >>>
    call atomic_acquire_1(i, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    // <<< injected gate
    assume owner[i] == tid && lock[i] == tid;
    assume 0 <= i && i < max;
    assume !valid[i];
    assume tid != nil && tid != done;
    // injected gate >>>
    call atomic_setEltToNull_1(i, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    // <<< injected gate
    assume 0 <= i && i < max;
    assume lock[i] == tid;
    assume tid != nil && tid != done;
    // injected gate >>>
    call atomic_release_1(i, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    result := false;
    goto anon6_Then27, CallToYieldProc;

  anon5_Then6:
    return;

  anon5_Then2:
    call og_Yield12_1();
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon5_Then6, CallToYieldProc;

  CallToYieldProc:
    call og_yield_1(linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation LookUp_1(x: int, tid: X, old_valid: [int]bool, old_elt: [int]int) returns (found: bool)
{
  var j: int;
  var isThere: bool;
  var og_global_old_elt: [int]int;
  var og_global_old_valid: [int]bool;
  var og_global_old_lock: [int]X;
  var og_global_old_owner: [int]X;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_tid_available: [X]bool;

  /*** structured program:
    j := 0;
    while (j < max)
      invariant Inv(valid, elt, owner);
      invariant (forall ii: int :: 0 <= ii && ii < j ==> !(old_valid[ii] && old_elt[ii] == x));
      invariant (forall ii: int :: 
        0 <= ii && ii < max && old_valid[ii] ==> valid[ii] && old_elt[ii] == elt[ii]);
      invariant 0 <= j;
    {
        call acquire(j, tid);
        call isThere := isEltThereAndValid(j, x, tid);
        if (isThere)
        {
            call release(j, tid);
            found := true;
            return;
        }

        call release(j, tid);
        j := j + 1;
    }

    found := false;
    return;
  **** end structured program */

  og_init:
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon5_LoopHead:
    assume linear_tid_available
       == linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false));
    assume elt == og_global_old_elt;
    assume valid == og_global_old_valid;
    assume lock == og_global_old_lock;
    assume owner == og_global_old_owner;
    assume pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assert Inv(valid, elt, owner);
    assert (forall ii: int :: 0 <= ii && ii < j ==> !(old_valid[ii] && old_elt[ii] == x));
    assert (forall ii: int :: 
      0 <= ii && ii < max && old_valid[ii] ==> valid[ii] && old_elt[ii] == elt[ii]);
    assert 0 <= j;
    goto anon5_LoopDone, anon5_LoopBody;

  anon5_LoopBody:
    assume {:partition} j < max;
    // <<< injected gate
    assume 0 <= j && j < max;
    assume tid != nil && tid != done;
    // injected gate >>>
    call atomic_acquire_1(j, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    // <<< injected gate
    assume 0 <= j && j < max;
    assume lock[j] == tid;
    assume tid != nil && tid != done;
    // injected gate >>>
    call isThere := atomic_isEltThereAndValid_1(j, x, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon6_Then, anon6_Else;

  anon6_Else:
    assume {:partition} !isThere;
    goto anon3;

  anon3:
    // <<< injected gate
    assume 0 <= j && j < max;
    assume lock[j] == tid;
    assume tid != nil && tid != done;
    // injected gate >>>
    call atomic_release_1(j, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon37, CallToYieldProc;

  anon6_Then:
    assume {:partition} isThere;
    // <<< injected gate
    assume 0 <= j && j < max;
    assume lock[j] == tid;
    assume tid != nil && tid != done;
    // injected gate >>>
    call atomic_release_1(j, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    found := true;
    goto anon6_Then9, CallToYieldProc;

  anon5_LoopDone:
    assume {:partition} max <= j;
    goto anon4;

  anon4:
    found := false;
    goto anon41, CallToYieldProc;

  anon05:
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    goto anon5_LoopHead;

  anon00:
    call og_Yield12_1_YieldLookUp_1(old_valid, old_elt);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    j := 0;
    goto anon05, CallToYieldProc;

  anon312:
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    goto anon5_LoopHead;

  anon37:
    call og_Yield12_1_YieldLookUp_1(old_valid, old_elt);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    j := j + 1;
    goto anon312, CallToYieldProc;

  anon6_Then13:
    return;

  anon6_Then9:
    call og_Yield12_1_YieldLookUp_1(old_valid, old_elt);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon6_Then13, CallToYieldProc;

  anon45:
    return;

  anon41:
    call og_Yield12_1_YieldLookUp_1(old_valid, old_elt);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon45, CallToYieldProc;

  CallToYieldProc:
    call og_yield_1(linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation Yield1_1()
{
  var og_global_old_elt: [int]int;
  var og_global_old_valid: [int]bool;
  var og_global_old_lock: [int]X;
  var og_global_old_owner: [int]X;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;
  var linear_tid_available: [X]bool;

  /*** structured program:
    yield;
    assert Inv(valid, elt, owner);
  **** end structured program */

  og_init:
    og_pc, og_ok, linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := false, false, linear_tid_MapConstBool(false), elt, valid, lock, owner, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assert Inv(valid, elt, owner);
    goto anon01, CallToYieldProc;

  anon09:
    assert og_pc
       || 
      (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_pc
       ==> elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_ok;
    return;

  anon01:
    assert og_pc
       || 
      (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_pc
       ==> elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    havoc elt, valid, lock, owner, pendingAsyncMultiset;
    assume true;
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapConstBool(false), elt, valid, lock, owner, pendingAsyncMultiset;
    assume Inv(valid, elt, owner);
    goto anon09, CallToYieldProc;

  CallToYieldProc:
    call og_yield_1(linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation Yield12_1()
{
  var og_global_old_elt: [int]int;
  var og_global_old_valid: [int]bool;
  var og_global_old_lock: [int]X;
  var og_global_old_owner: [int]X;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_tid_available: [X]bool;

  /*** structured program:
    yield;
    assert Inv(valid, elt, owner);
  **** end structured program */

  og_init:
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapConstBool(false), elt, valid, lock, owner, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assert Inv(valid, elt, owner);
    goto anon01, CallToYieldProc;

  anon05:
    return;

  anon01:
    havoc elt, valid, lock, owner, pendingAsyncMultiset;
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapConstBool(false), elt, valid, lock, owner, pendingAsyncMultiset;
    assume Inv(valid, elt, owner);
    goto anon05, CallToYieldProc;

  CallToYieldProc:
    call og_yield_1(linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation YieldLookUp_1(old_valid: [int]bool, old_elt: [int]int)
{
  var og_global_old_elt: [int]int;
  var og_global_old_valid: [int]bool;
  var og_global_old_lock: [int]X;
  var og_global_old_owner: [int]X;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_tid_available: [X]bool;

  /*** structured program:
    yield;
    assert (forall ii: int :: 
      0 <= ii && ii < max && old_valid[ii] ==> valid[ii] && old_elt[ii] == elt[ii]);
  **** end structured program */

  og_init:
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapConstBool(false), elt, valid, lock, owner, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assert (forall ii: int :: 
      0 <= ii && ii < max && old_valid[ii] ==> valid[ii] && old_elt[ii] == elt[ii]);
    goto anon01, CallToYieldProc;

  anon05:
    return;

  anon01:
    havoc elt, valid, lock, owner, pendingAsyncMultiset;
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapConstBool(false), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (forall ii: int :: 
      0 <= ii && ii < max && old_valid[ii] ==> valid[ii] && old_elt[ii] == elt[ii]);
    goto anon05, CallToYieldProc;

  CallToYieldProc:
    call og_yield_1(linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



procedure {:inline 1} Impl_YieldChecker_Yield1_1(linear_tid_in: [X]bool, 
    og_global_old_elt: [int]int, 
    og_global_old_valid: [int]bool, 
    og_global_old_lock: [int]X, 
    og_global_old_owner: [int]X, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_Yield12_1(linear_tid_in: [X]bool, 
    og_global_old_elt: [int]int, 
    og_global_old_valid: [int]bool, 
    og_global_old_lock: [int]X, 
    og_global_old_owner: [int]X, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_YieldLookUp_1(linear_tid_in: [X]bool, 
    og_global_old_elt: [int]int, 
    og_global_old_valid: [int]bool, 
    og_global_old_lock: [int]X, 
    og_global_old_owner: [int]X, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



implementation {:inline 1} Impl_YieldChecker_Yield1_1(linear_tid_in: [X]bool, 
    og_global_old_elt: [int]int, 
    og_global_old_valid: [int]bool, 
    og_global_old_lock: [int]X, 
    og_global_old_owner: [int]X, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var og_local_old_elt: [int]int;
  var og_local_old_valid: [int]bool;
  var og_local_old_lock: [int]X;
  var og_local_old_owner: [int]X;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume Inv(og_global_old_valid, og_global_old_elt, og_global_old_owner);
    assert Inv(valid, elt, owner);
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_Yield12_1(linear_tid_in: [X]bool, 
    og_global_old_elt: [int]int, 
    og_global_old_valid: [int]bool, 
    og_global_old_lock: [int]X, 
    og_global_old_owner: [int]X, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var og_local_old_elt: [int]int;
  var og_local_old_valid: [int]bool;
  var og_local_old_lock: [int]X;
  var og_local_old_owner: [int]X;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume Inv(og_global_old_valid, og_global_old_elt, og_global_old_owner);
    assert Inv(valid, elt, owner);
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_YieldLookUp_1(linear_tid_in: [X]bool, 
    og_global_old_elt: [int]int, 
    og_global_old_valid: [int]bool, 
    og_global_old_lock: [int]X, 
    og_global_old_owner: [int]X, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var old_valid: [int]bool;
  var old_elt: [int]int;
  var og_local_old_elt: [int]int;
  var og_local_old_valid: [int]bool;
  var og_local_old_lock: [int]X;
  var og_local_old_owner: [int]X;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (forall ii: int :: 
      0 <= ii && ii < max && old_valid[ii]
         ==> og_global_old_valid[ii] && old_elt[ii] == og_global_old_elt[ii]);
    assert (forall ii: int :: 
      0 <= ii && ii < max && old_valid[ii] ==> valid[ii] && old_elt[ii] == elt[ii]);
    assume false;
    return;
}



procedure og_Yield1_1();
  requires Inv(valid, elt, owner);
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures Inv(valid, elt, owner);



procedure og_Yield12_1();
  requires Inv(valid, elt, owner);
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures Inv(valid, elt, owner);



procedure og_Yield12_1_YieldLookUp_1(og_1_old_valid: [int]bool, og_1_old_elt: [int]int);
  requires Inv(valid, elt, owner);
  requires (forall ii: int :: 
    0 <= ii && ii < max && og_1_old_valid[ii]
       ==> valid[ii] && og_1_old_elt[ii] == elt[ii]);
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures Inv(valid, elt, owner);
  ensures (forall ii: int :: 
    0 <= ii && ii < max && og_1_old_valid[ii]
       ==> valid[ii] && og_1_old_elt[ii] == elt[ii]);



procedure {:inline 1} og_yield_1(linear_tid_in: [X]bool, 
    og_global_old_elt: [int]int, 
    og_global_old_valid: [int]bool, 
    og_global_old_lock: [int]X, 
    og_global_old_owner: [int]X, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



implementation {:inline 1} og_yield_1(linear_tid_in: [X]bool, 
    og_global_old_elt: [int]int, 
    og_global_old_valid: [int]bool, 
    og_global_old_lock: [int]X, 
    og_global_old_owner: [int]X, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{

  enter:
    goto L_0, L_1, L_2;

  L_0:
    call Impl_YieldChecker_Yield1_1(linear_tid_in, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset);
    return;

  L_1:
    call Impl_YieldChecker_Yield12_1(linear_tid_in, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset);
    return;

  L_2:
    call Impl_YieldChecker_YieldLookUp_1(linear_tid_in, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset);
    return;
}



procedure Insert_2(x: int, tid: X) returns (result: bool);
  requires Inv(valid, elt, owner) && x != null && tid != nil && tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures Inv(valid, elt, owner);



procedure InsertPair_2(x: int, y: int, tid: X) returns (result: bool);
  requires Inv(valid, elt, owner) && x != null && y != null && tid != nil && tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures Inv(valid, elt, owner);



procedure LookUp_2(x: int, tid: X, old_valid: [int]bool, old_elt: [int]int) returns (found: bool);
  requires old_valid == valid && old_elt == elt;
  requires Inv(valid, elt, owner);
  requires tid != nil && tid != done;
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures Inv(valid, elt, owner);



procedure Yield12_2();
  requires Inv(valid, elt, owner);
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures Inv(valid, elt, owner);



procedure YieldLookUp_2(old_valid: [int]bool, old_elt: [int]int);
  requires (forall ii: int :: 
    0 <= ii && ii < max && old_valid[ii] ==> valid[ii] && old_elt[ii] == elt[ii]);
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures (forall ii: int :: 
    0 <= ii && ii < max && old_valid[ii] ==> valid[ii] && old_elt[ii] == elt[ii]);



implementation Insert_2(x: int, tid: X) returns (result: bool)
{
  var i: int;
  var og_global_old_elt: [int]int;
  var og_global_old_valid: [int]bool;
  var og_global_old_lock: [int]X;
  var og_global_old_owner: [int]X;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;
  var og_old_result: bool;
  var linear_tid_available: [X]bool;

  /*** structured program:
    call i := FindSlot(x, tid);
    if (i == -1)
    {
        result := false;
        return;
    }

    assert i != -1;
    assert i != -1;
    call acquire(i, tid);
    assert elt[i] == x;
    assert valid[i] <==> false;
    call setValid(i, tid);
    call release(i, tid);
    result := true;
    return;
  **** end structured program */

  og_init:
    og_pc, og_ok, linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset, og_old_result := false, false, linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset, result;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon3_Else:
    assume {:partition} i != -1;
    goto anon2;

  anon2:
    call skip_dummy_Yield1();
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assert i != -1;
    // <<< injected gate
    assert 0 <= i && i < max;
    assert tid != nil && tid != done;
    // injected gate >>>
    call atomic_acquire_2(i, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assert elt[i] == x;
    assert valid[i] <==> false;
    // <<< injected gate
    assert 0 <= i && i < max;
    assert lock[i] == tid;
    assert tid != nil && tid != done;
    assert owner[i] == tid;
    // injected gate >>>
    call atomic_setValid_2(i, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    // <<< injected gate
    assert 0 <= i && i < max;
    assert lock[i] == tid;
    assert tid != nil && tid != done;
    // injected gate >>>
    call atomic_release_2(i, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    result := true;
    goto anon227, CallToYieldProc;

  anon3_Then:
    assume {:partition} i == -1;
    result := false;
    goto anon3_Then2, CallToYieldProc;

  anon00:
    assert og_pc
       || 
      (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_r: int :: 
        elt == og_global_old_elt[#tmp_0_second_r := x]
           && valid == og_global_old_valid[#tmp_0_second_r := true]
           && lock == og_global_old_lock
           && owner == og_global_old_owner[#tmp_0_second_r := done]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (result <==> true)
           && og_global_old_owner[#tmp_0_second_r] == nil
           && og_global_old_elt[#tmp_0_second_r] == null
           && (og_global_old_valid[#tmp_0_second_r] <==> false)
           && 0 <= #tmp_0_second_r
           && #tmp_0_second_r < max)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> false));
    assert og_pc
       ==> elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> og_old_result);
    og_pc, og_ok := elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_r: int :: 
        elt == og_global_old_elt[#tmp_0_second_r := x]
           && valid == og_global_old_valid[#tmp_0_second_r := true]
           && lock == og_global_old_lock
           && owner == og_global_old_owner[#tmp_0_second_r := done]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (result <==> true)
           && og_global_old_owner[#tmp_0_second_r] == nil
           && og_global_old_elt[#tmp_0_second_r] == null
           && (og_global_old_valid[#tmp_0_second_r] <==> false)
           && 0 <= #tmp_0_second_r
           && #tmp_0_second_r < max)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> false));
    call og_Yield12_2();
    assume og_pc || true;
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset, og_old_result := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset, result;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    // <<< injected gate
    assert tid != nil && tid != done;
    assert x != null;
    // injected gate >>>
    call i := AtomicFindSlot_2(x, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon3_Then, anon3_Else;

  anon235:
    assert og_pc
       || 
      (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_r: int :: 
        elt == og_global_old_elt[#tmp_0_second_r := x]
           && valid == og_global_old_valid[#tmp_0_second_r := true]
           && lock == og_global_old_lock
           && owner == og_global_old_owner[#tmp_0_second_r := done]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (result <==> true)
           && og_global_old_owner[#tmp_0_second_r] == nil
           && og_global_old_elt[#tmp_0_second_r] == null
           && (og_global_old_valid[#tmp_0_second_r] <==> false)
           && 0 <= #tmp_0_second_r
           && #tmp_0_second_r < max)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> false));
    assert og_pc
       ==> elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> og_old_result);
    og_pc, og_ok := elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_r: int :: 
        elt == og_global_old_elt[#tmp_0_second_r := x]
           && valid == og_global_old_valid[#tmp_0_second_r := true]
           && lock == og_global_old_lock
           && owner == og_global_old_owner[#tmp_0_second_r := done]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (result <==> true)
           && og_global_old_owner[#tmp_0_second_r] == nil
           && og_global_old_elt[#tmp_0_second_r] == null
           && (og_global_old_valid[#tmp_0_second_r] <==> false)
           && 0 <= #tmp_0_second_r
           && #tmp_0_second_r < max)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> false));
    assert og_ok;
    return;

  anon227:
    assert og_pc
       || 
      (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_r: int :: 
        elt == og_global_old_elt[#tmp_0_second_r := x]
           && valid == og_global_old_valid[#tmp_0_second_r := true]
           && lock == og_global_old_lock
           && owner == og_global_old_owner[#tmp_0_second_r := done]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (result <==> true)
           && og_global_old_owner[#tmp_0_second_r] == nil
           && og_global_old_elt[#tmp_0_second_r] == null
           && (og_global_old_valid[#tmp_0_second_r] <==> false)
           && 0 <= #tmp_0_second_r
           && #tmp_0_second_r < max)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> false));
    assert og_pc
       ==> elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> og_old_result);
    og_pc, og_ok := elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_r: int :: 
        elt == og_global_old_elt[#tmp_0_second_r := x]
           && valid == og_global_old_valid[#tmp_0_second_r := true]
           && lock == og_global_old_lock
           && owner == og_global_old_owner[#tmp_0_second_r := done]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (result <==> true)
           && og_global_old_owner[#tmp_0_second_r] == nil
           && og_global_old_elt[#tmp_0_second_r] == null
           && (og_global_old_valid[#tmp_0_second_r] <==> false)
           && 0 <= #tmp_0_second_r
           && #tmp_0_second_r < max)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> false));
    call og_Yield12_2();
    assume og_pc || true;
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset, og_old_result := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset, result;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon235, CallToYieldProc;

  anon3_Then10:
    assert og_pc
       || 
      (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_r: int :: 
        elt == og_global_old_elt[#tmp_0_second_r := x]
           && valid == og_global_old_valid[#tmp_0_second_r := true]
           && lock == og_global_old_lock
           && owner == og_global_old_owner[#tmp_0_second_r := done]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (result <==> true)
           && og_global_old_owner[#tmp_0_second_r] == nil
           && og_global_old_elt[#tmp_0_second_r] == null
           && (og_global_old_valid[#tmp_0_second_r] <==> false)
           && 0 <= #tmp_0_second_r
           && #tmp_0_second_r < max)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> false));
    assert og_pc
       ==> elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> og_old_result);
    og_pc, og_ok := elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_r: int :: 
        elt == og_global_old_elt[#tmp_0_second_r := x]
           && valid == og_global_old_valid[#tmp_0_second_r := true]
           && lock == og_global_old_lock
           && owner == og_global_old_owner[#tmp_0_second_r := done]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (result <==> true)
           && og_global_old_owner[#tmp_0_second_r] == nil
           && og_global_old_elt[#tmp_0_second_r] == null
           && (og_global_old_valid[#tmp_0_second_r] <==> false)
           && 0 <= #tmp_0_second_r
           && #tmp_0_second_r < max)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> false));
    assert og_ok;
    return;

  anon3_Then2:
    assert og_pc
       || 
      (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_r: int :: 
        elt == og_global_old_elt[#tmp_0_second_r := x]
           && valid == og_global_old_valid[#tmp_0_second_r := true]
           && lock == og_global_old_lock
           && owner == og_global_old_owner[#tmp_0_second_r := done]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (result <==> true)
           && og_global_old_owner[#tmp_0_second_r] == nil
           && og_global_old_elt[#tmp_0_second_r] == null
           && (og_global_old_valid[#tmp_0_second_r] <==> false)
           && 0 <= #tmp_0_second_r
           && #tmp_0_second_r < max)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> false));
    assert og_pc
       ==> elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> og_old_result);
    og_pc, og_ok := elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_r: int :: 
        elt == og_global_old_elt[#tmp_0_second_r := x]
           && valid == og_global_old_valid[#tmp_0_second_r := true]
           && lock == og_global_old_lock
           && owner == og_global_old_owner[#tmp_0_second_r := done]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (result <==> true)
           && og_global_old_owner[#tmp_0_second_r] == nil
           && og_global_old_elt[#tmp_0_second_r] == null
           && (og_global_old_valid[#tmp_0_second_r] <==> false)
           && 0 <= #tmp_0_second_r
           && #tmp_0_second_r < max)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> false));
    call og_Yield12_2();
    assume og_pc || true;
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset, og_old_result := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset, result;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon3_Then10, CallToYieldProc;

  CallToYieldProc:
    call og_yield_2(linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation InsertPair_2(x: int, y: int, tid: X) returns (result: bool)
{
  var i: int;
  var j: int;
  var og_global_old_elt: [int]int;
  var og_global_old_valid: [int]bool;
  var og_global_old_lock: [int]X;
  var og_global_old_owner: [int]X;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;
  var og_old_result: bool;
  var linear_tid_available: [X]bool;

  /*** structured program:
    call i := FindSlot(x, tid);
    if (i == -1)
    {
        result := false;
        return;
    }

    call j := FindSlot(y, tid);
    if (j == -1)
    {
        call acquire(i, tid);
        call setEltToNull(i, tid);
        call release(i, tid);
        result := false;
        return;
    }

    assert i != -1 && j != -1;
    call acquire(i, tid);
    call acquire(j, tid);
    assert elt[i] == x;
    assert elt[j] == y;
    assert valid[i] <==> false;
    assert valid[j] <==> false;
    call setValid(i, tid);
    call setValid(j, tid);
    call release(j, tid);
    call release(i, tid);
    result := true;
    return;
  **** end structured program */

  og_init:
    og_pc, og_ok, linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset, og_old_result := false, false, linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset, result;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon5_Else:
    assume {:partition} i != -1;
    goto anon2;

  anon2:
    call skip_dummy_Yield1();
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    // <<< injected gate
    assert tid != nil && tid != done;
    assert y != null;
    // injected gate >>>
    call j := AtomicFindSlot_2(y, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon6_Then, anon6_Else;

  anon6_Else:
    assume {:partition} j != -1;
    goto anon4;

  anon4:
    call skip_dummy_Yield1();
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assert i != -1 && j != -1;
    // <<< injected gate
    assert 0 <= i && i < max;
    assert tid != nil && tid != done;
    // injected gate >>>
    call atomic_acquire_2(i, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    // <<< injected gate
    assert 0 <= j && j < max;
    assert tid != nil && tid != done;
    // injected gate >>>
    call atomic_acquire_2(j, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assert elt[i] == x;
    assert elt[j] == y;
    assert valid[i] <==> false;
    assert valid[j] <==> false;
    // <<< injected gate
    assert 0 <= i && i < max;
    assert lock[i] == tid;
    assert tid != nil && tid != done;
    assert owner[i] == tid;
    // injected gate >>>
    call atomic_setValid_2(i, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    // <<< injected gate
    assert 0 <= j && j < max;
    assert lock[j] == tid;
    assert tid != nil && tid != done;
    assert owner[j] == tid;
    // injected gate >>>
    call atomic_setValid_2(j, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    // <<< injected gate
    assert 0 <= j && j < max;
    assert lock[j] == tid;
    assert tid != nil && tid != done;
    // injected gate >>>
    call atomic_release_2(j, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    // <<< injected gate
    assert 0 <= i && i < max;
    assert lock[i] == tid;
    assert tid != nil && tid != done;
    // injected gate >>>
    call atomic_release_2(i, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    result := true;
    goto anon450, CallToYieldProc;

  anon6_Then:
    assume {:partition} j == -1;
    call skip_dummy_Yield1();
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    // <<< injected gate
    assert 0 <= i && i < max;
    assert tid != nil && tid != done;
    // injected gate >>>
    call atomic_acquire_2(i, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    // <<< injected gate
    assert owner[i] == tid && lock[i] == tid;
    assert 0 <= i && i < max;
    assert !valid[i];
    assert tid != nil && tid != done;
    // injected gate >>>
    call atomic_setEltToNull_2(i, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    // <<< injected gate
    assert 0 <= i && i < max;
    assert lock[i] == tid;
    assert tid != nil && tid != done;
    // injected gate >>>
    call atomic_release_2(i, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    result := false;
    goto anon6_Then25, CallToYieldProc;

  anon5_Then:
    assume {:partition} i == -1;
    result := false;
    goto anon5_Then2, CallToYieldProc;

  anon00:
    assert og_pc
       || 
      (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_rx: int, #tmp_1_second_ry: int :: 
        elt == og_global_old_elt[#tmp_0_second_rx := x][#tmp_1_second_ry := y]
           && valid == og_global_old_valid[#tmp_0_second_rx := true][#tmp_1_second_ry := true]
           && lock == og_global_old_lock
           && owner == og_global_old_owner[#tmp_0_second_rx := done][#tmp_1_second_ry := done]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (result <==> true)
           && og_global_old_elt[#tmp_0_second_rx] == null
           && og_global_old_elt[#tmp_0_second_rx] == null
           && (og_global_old_valid[#tmp_1_second_ry] <==> false)
           && (og_global_old_valid[#tmp_0_second_rx] <==> false)
           && 0 <= #tmp_0_second_rx
           && #tmp_0_second_rx < max
           && 0 <= #tmp_1_second_ry
           && #tmp_1_second_ry < max
           && #tmp_0_second_rx != #tmp_1_second_ry)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> false));
    assert og_pc
       ==> elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> og_old_result);
    og_pc, og_ok := elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_rx: int, #tmp_1_second_ry: int :: 
        elt == og_global_old_elt[#tmp_0_second_rx := x][#tmp_1_second_ry := y]
           && valid == og_global_old_valid[#tmp_0_second_rx := true][#tmp_1_second_ry := true]
           && lock == og_global_old_lock
           && owner == og_global_old_owner[#tmp_0_second_rx := done][#tmp_1_second_ry := done]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (result <==> true)
           && og_global_old_elt[#tmp_0_second_rx] == null
           && og_global_old_elt[#tmp_0_second_rx] == null
           && (og_global_old_valid[#tmp_1_second_ry] <==> false)
           && (og_global_old_valid[#tmp_0_second_rx] <==> false)
           && 0 <= #tmp_0_second_rx
           && #tmp_0_second_rx < max
           && 0 <= #tmp_1_second_ry
           && #tmp_1_second_ry < max
           && #tmp_0_second_rx != #tmp_1_second_ry)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> false));
    call og_Yield12_2();
    assume og_pc || true;
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset, og_old_result := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset, result;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    // <<< injected gate
    assert tid != nil && tid != done;
    assert x != null;
    // injected gate >>>
    call i := AtomicFindSlot_2(x, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon5_Then, anon5_Else;

  anon458:
    assert og_pc
       || 
      (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_rx: int, #tmp_1_second_ry: int :: 
        elt == og_global_old_elt[#tmp_0_second_rx := x][#tmp_1_second_ry := y]
           && valid == og_global_old_valid[#tmp_0_second_rx := true][#tmp_1_second_ry := true]
           && lock == og_global_old_lock
           && owner == og_global_old_owner[#tmp_0_second_rx := done][#tmp_1_second_ry := done]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (result <==> true)
           && og_global_old_elt[#tmp_0_second_rx] == null
           && og_global_old_elt[#tmp_0_second_rx] == null
           && (og_global_old_valid[#tmp_1_second_ry] <==> false)
           && (og_global_old_valid[#tmp_0_second_rx] <==> false)
           && 0 <= #tmp_0_second_rx
           && #tmp_0_second_rx < max
           && 0 <= #tmp_1_second_ry
           && #tmp_1_second_ry < max
           && #tmp_0_second_rx != #tmp_1_second_ry)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> false));
    assert og_pc
       ==> elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> og_old_result);
    og_pc, og_ok := elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_rx: int, #tmp_1_second_ry: int :: 
        elt == og_global_old_elt[#tmp_0_second_rx := x][#tmp_1_second_ry := y]
           && valid == og_global_old_valid[#tmp_0_second_rx := true][#tmp_1_second_ry := true]
           && lock == og_global_old_lock
           && owner == og_global_old_owner[#tmp_0_second_rx := done][#tmp_1_second_ry := done]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (result <==> true)
           && og_global_old_elt[#tmp_0_second_rx] == null
           && og_global_old_elt[#tmp_0_second_rx] == null
           && (og_global_old_valid[#tmp_1_second_ry] <==> false)
           && (og_global_old_valid[#tmp_0_second_rx] <==> false)
           && 0 <= #tmp_0_second_rx
           && #tmp_0_second_rx < max
           && 0 <= #tmp_1_second_ry
           && #tmp_1_second_ry < max
           && #tmp_0_second_rx != #tmp_1_second_ry)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> false));
    assert og_ok;
    return;

  anon450:
    assert og_pc
       || 
      (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_rx: int, #tmp_1_second_ry: int :: 
        elt == og_global_old_elt[#tmp_0_second_rx := x][#tmp_1_second_ry := y]
           && valid == og_global_old_valid[#tmp_0_second_rx := true][#tmp_1_second_ry := true]
           && lock == og_global_old_lock
           && owner == og_global_old_owner[#tmp_0_second_rx := done][#tmp_1_second_ry := done]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (result <==> true)
           && og_global_old_elt[#tmp_0_second_rx] == null
           && og_global_old_elt[#tmp_0_second_rx] == null
           && (og_global_old_valid[#tmp_1_second_ry] <==> false)
           && (og_global_old_valid[#tmp_0_second_rx] <==> false)
           && 0 <= #tmp_0_second_rx
           && #tmp_0_second_rx < max
           && 0 <= #tmp_1_second_ry
           && #tmp_1_second_ry < max
           && #tmp_0_second_rx != #tmp_1_second_ry)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> false));
    assert og_pc
       ==> elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> og_old_result);
    og_pc, og_ok := elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_rx: int, #tmp_1_second_ry: int :: 
        elt == og_global_old_elt[#tmp_0_second_rx := x][#tmp_1_second_ry := y]
           && valid == og_global_old_valid[#tmp_0_second_rx := true][#tmp_1_second_ry := true]
           && lock == og_global_old_lock
           && owner == og_global_old_owner[#tmp_0_second_rx := done][#tmp_1_second_ry := done]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (result <==> true)
           && og_global_old_elt[#tmp_0_second_rx] == null
           && og_global_old_elt[#tmp_0_second_rx] == null
           && (og_global_old_valid[#tmp_1_second_ry] <==> false)
           && (og_global_old_valid[#tmp_0_second_rx] <==> false)
           && 0 <= #tmp_0_second_rx
           && #tmp_0_second_rx < max
           && 0 <= #tmp_1_second_ry
           && #tmp_1_second_ry < max
           && #tmp_0_second_rx != #tmp_1_second_ry)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> false));
    call og_Yield12_2();
    assume og_pc || true;
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset, og_old_result := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset, result;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon458, CallToYieldProc;

  anon6_Then33:
    assert og_pc
       || 
      (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_rx: int, #tmp_1_second_ry: int :: 
        elt == og_global_old_elt[#tmp_0_second_rx := x][#tmp_1_second_ry := y]
           && valid == og_global_old_valid[#tmp_0_second_rx := true][#tmp_1_second_ry := true]
           && lock == og_global_old_lock
           && owner == og_global_old_owner[#tmp_0_second_rx := done][#tmp_1_second_ry := done]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (result <==> true)
           && og_global_old_elt[#tmp_0_second_rx] == null
           && og_global_old_elt[#tmp_0_second_rx] == null
           && (og_global_old_valid[#tmp_1_second_ry] <==> false)
           && (og_global_old_valid[#tmp_0_second_rx] <==> false)
           && 0 <= #tmp_0_second_rx
           && #tmp_0_second_rx < max
           && 0 <= #tmp_1_second_ry
           && #tmp_1_second_ry < max
           && #tmp_0_second_rx != #tmp_1_second_ry)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> false));
    assert og_pc
       ==> elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> og_old_result);
    og_pc, og_ok := elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_rx: int, #tmp_1_second_ry: int :: 
        elt == og_global_old_elt[#tmp_0_second_rx := x][#tmp_1_second_ry := y]
           && valid == og_global_old_valid[#tmp_0_second_rx := true][#tmp_1_second_ry := true]
           && lock == og_global_old_lock
           && owner == og_global_old_owner[#tmp_0_second_rx := done][#tmp_1_second_ry := done]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (result <==> true)
           && og_global_old_elt[#tmp_0_second_rx] == null
           && og_global_old_elt[#tmp_0_second_rx] == null
           && (og_global_old_valid[#tmp_1_second_ry] <==> false)
           && (og_global_old_valid[#tmp_0_second_rx] <==> false)
           && 0 <= #tmp_0_second_rx
           && #tmp_0_second_rx < max
           && 0 <= #tmp_1_second_ry
           && #tmp_1_second_ry < max
           && #tmp_0_second_rx != #tmp_1_second_ry)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> false));
    assert og_ok;
    return;

  anon6_Then25:
    assert og_pc
       || 
      (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_rx: int, #tmp_1_second_ry: int :: 
        elt == og_global_old_elt[#tmp_0_second_rx := x][#tmp_1_second_ry := y]
           && valid == og_global_old_valid[#tmp_0_second_rx := true][#tmp_1_second_ry := true]
           && lock == og_global_old_lock
           && owner == og_global_old_owner[#tmp_0_second_rx := done][#tmp_1_second_ry := done]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (result <==> true)
           && og_global_old_elt[#tmp_0_second_rx] == null
           && og_global_old_elt[#tmp_0_second_rx] == null
           && (og_global_old_valid[#tmp_1_second_ry] <==> false)
           && (og_global_old_valid[#tmp_0_second_rx] <==> false)
           && 0 <= #tmp_0_second_rx
           && #tmp_0_second_rx < max
           && 0 <= #tmp_1_second_ry
           && #tmp_1_second_ry < max
           && #tmp_0_second_rx != #tmp_1_second_ry)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> false));
    assert og_pc
       ==> elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> og_old_result);
    og_pc, og_ok := elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_rx: int, #tmp_1_second_ry: int :: 
        elt == og_global_old_elt[#tmp_0_second_rx := x][#tmp_1_second_ry := y]
           && valid == og_global_old_valid[#tmp_0_second_rx := true][#tmp_1_second_ry := true]
           && lock == og_global_old_lock
           && owner == og_global_old_owner[#tmp_0_second_rx := done][#tmp_1_second_ry := done]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (result <==> true)
           && og_global_old_elt[#tmp_0_second_rx] == null
           && og_global_old_elt[#tmp_0_second_rx] == null
           && (og_global_old_valid[#tmp_1_second_ry] <==> false)
           && (og_global_old_valid[#tmp_0_second_rx] <==> false)
           && 0 <= #tmp_0_second_rx
           && #tmp_0_second_rx < max
           && 0 <= #tmp_1_second_ry
           && #tmp_1_second_ry < max
           && #tmp_0_second_rx != #tmp_1_second_ry)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> false));
    call og_Yield12_2();
    assume og_pc || true;
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset, og_old_result := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset, result;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon6_Then33, CallToYieldProc;

  anon5_Then10:
    assert og_pc
       || 
      (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_rx: int, #tmp_1_second_ry: int :: 
        elt == og_global_old_elt[#tmp_0_second_rx := x][#tmp_1_second_ry := y]
           && valid == og_global_old_valid[#tmp_0_second_rx := true][#tmp_1_second_ry := true]
           && lock == og_global_old_lock
           && owner == og_global_old_owner[#tmp_0_second_rx := done][#tmp_1_second_ry := done]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (result <==> true)
           && og_global_old_elt[#tmp_0_second_rx] == null
           && og_global_old_elt[#tmp_0_second_rx] == null
           && (og_global_old_valid[#tmp_1_second_ry] <==> false)
           && (og_global_old_valid[#tmp_0_second_rx] <==> false)
           && 0 <= #tmp_0_second_rx
           && #tmp_0_second_rx < max
           && 0 <= #tmp_1_second_ry
           && #tmp_1_second_ry < max
           && #tmp_0_second_rx != #tmp_1_second_ry)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> false));
    assert og_pc
       ==> elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> og_old_result);
    og_pc, og_ok := elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_rx: int, #tmp_1_second_ry: int :: 
        elt == og_global_old_elt[#tmp_0_second_rx := x][#tmp_1_second_ry := y]
           && valid == og_global_old_valid[#tmp_0_second_rx := true][#tmp_1_second_ry := true]
           && lock == og_global_old_lock
           && owner == og_global_old_owner[#tmp_0_second_rx := done][#tmp_1_second_ry := done]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (result <==> true)
           && og_global_old_elt[#tmp_0_second_rx] == null
           && og_global_old_elt[#tmp_0_second_rx] == null
           && (og_global_old_valid[#tmp_1_second_ry] <==> false)
           && (og_global_old_valid[#tmp_0_second_rx] <==> false)
           && 0 <= #tmp_0_second_rx
           && #tmp_0_second_rx < max
           && 0 <= #tmp_1_second_ry
           && #tmp_1_second_ry < max
           && #tmp_0_second_rx != #tmp_1_second_ry)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> false));
    assert og_ok;
    return;

  anon5_Then2:
    assert og_pc
       || 
      (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_rx: int, #tmp_1_second_ry: int :: 
        elt == og_global_old_elt[#tmp_0_second_rx := x][#tmp_1_second_ry := y]
           && valid == og_global_old_valid[#tmp_0_second_rx := true][#tmp_1_second_ry := true]
           && lock == og_global_old_lock
           && owner == og_global_old_owner[#tmp_0_second_rx := done][#tmp_1_second_ry := done]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (result <==> true)
           && og_global_old_elt[#tmp_0_second_rx] == null
           && og_global_old_elt[#tmp_0_second_rx] == null
           && (og_global_old_valid[#tmp_1_second_ry] <==> false)
           && (og_global_old_valid[#tmp_0_second_rx] <==> false)
           && 0 <= #tmp_0_second_rx
           && #tmp_0_second_rx < max
           && 0 <= #tmp_1_second_ry
           && #tmp_1_second_ry < max
           && #tmp_0_second_rx != #tmp_1_second_ry)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> false));
    assert og_pc
       ==> elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> og_old_result);
    og_pc, og_ok := elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_rx: int, #tmp_1_second_ry: int :: 
        elt == og_global_old_elt[#tmp_0_second_rx := x][#tmp_1_second_ry := y]
           && valid == og_global_old_valid[#tmp_0_second_rx := true][#tmp_1_second_ry := true]
           && lock == og_global_old_lock
           && owner == og_global_old_owner[#tmp_0_second_rx := done][#tmp_1_second_ry := done]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (result <==> true)
           && og_global_old_elt[#tmp_0_second_rx] == null
           && og_global_old_elt[#tmp_0_second_rx] == null
           && (og_global_old_valid[#tmp_1_second_ry] <==> false)
           && (og_global_old_valid[#tmp_0_second_rx] <==> false)
           && 0 <= #tmp_0_second_rx
           && #tmp_0_second_rx < max
           && 0 <= #tmp_1_second_ry
           && #tmp_1_second_ry < max
           && #tmp_0_second_rx != #tmp_1_second_ry)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (result <==> false));
    call og_Yield12_2();
    assume og_pc || true;
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset, og_old_result := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset, result;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon5_Then10, CallToYieldProc;

  CallToYieldProc:
    call og_yield_2(linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation LookUp_2(x: int, tid: X, old_valid: [int]bool, old_elt: [int]int) returns (found: bool)
{
  var j: int;
  var isThere: bool;
  var og_global_old_elt: [int]int;
  var og_global_old_valid: [int]bool;
  var og_global_old_lock: [int]X;
  var og_global_old_owner: [int]X;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;
  var og_old_found: bool;
  var linear_tid_available: [X]bool;
  var og_pc_anon5_LoopHead: bool;
  var og_ok_anon5_LoopHead: bool;

  /*** structured program:
    j := 0;
    while (j < max)
      invariant Inv(valid, elt, owner);
      invariant (forall ii: int :: 0 <= ii && ii < j ==> !(old_valid[ii] && old_elt[ii] == x));
      invariant (forall ii: int :: 
        0 <= ii && ii < max && old_valid[ii] ==> valid[ii] && old_elt[ii] == elt[ii]);
      invariant 0 <= j;
    {
        call acquire(j, tid);
        call isThere := isEltThereAndValid(j, x, tid);
        if (isThere)
        {
            call release(j, tid);
            found := true;
            return;
        }

        call release(j, tid);
        j := j + 1;
    }

    found := false;
    return;
  **** end structured program */

  og_init:
    og_pc, og_pc_anon5_LoopHead, og_ok, og_ok_anon5_LoopHead, linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset, og_old_found := false, false, false, false, linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset, found;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon5_LoopHead:
    assert og_pc_anon5_LoopHead == og_pc;
    assert og_ok_anon5_LoopHead ==> og_ok;
    assume linear_tid_available
       == linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false));
    assume elt == og_global_old_elt;
    assume valid == og_global_old_valid;
    assume lock == og_global_old_lock;
    assume owner == og_global_old_owner;
    assume pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assume found == og_old_found;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assert Inv(valid, elt, owner);
    assert (forall ii: int :: 0 <= ii && ii < j ==> !(old_valid[ii] && old_elt[ii] == x));
    assert (forall ii: int :: 
      0 <= ii && ii < max && old_valid[ii] ==> valid[ii] && old_elt[ii] == elt[ii]);
    assert 0 <= j;
    goto anon5_LoopDone, anon5_LoopBody;

  anon5_LoopBody:
    assume {:partition} j < max;
    // <<< injected gate
    assert 0 <= j && j < max;
    assert tid != nil && tid != done;
    // injected gate >>>
    call atomic_acquire_2(j, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    // <<< injected gate
    assert 0 <= j && j < max;
    assert lock[j] == tid;
    assert tid != nil && tid != done;
    // injected gate >>>
    call isThere := atomic_isEltThereAndValid_2(j, x, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon6_Then, anon6_Else;

  anon6_Else:
    assume {:partition} !isThere;
    goto anon3;

  anon3:
    // <<< injected gate
    assert 0 <= j && j < max;
    assert lock[j] == tid;
    assert tid != nil && tid != done;
    // injected gate >>>
    call atomic_release_2(j, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon37, CallToYieldProc;

  anon6_Then:
    assume {:partition} isThere;
    // <<< injected gate
    assert 0 <= j && j < max;
    assert lock[j] == tid;
    assert tid != nil && tid != done;
    // injected gate >>>
    call atomic_release_2(j, tid);
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    found := true;
    goto anon6_Then9, CallToYieldProc;

  anon5_LoopDone:
    assume {:partition} max <= j;
    goto anon4;

  anon4:
    found := false;
    goto anon41, CallToYieldProc;

  anon09:
    assert og_pc
       || 
      (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (found <==> found)
         && (!found
           ==> (forall second_ii: int :: 
            0 <= second_ii && second_ii < max
               ==> !(old_valid[second_ii] && old_elt[second_ii] == x)))
         && (found
           ==> (exists second_ii: int :: 
            0 <= second_ii
               && second_ii < max
               && og_global_old_valid[second_ii]
               && og_global_old_elt[second_ii] == x)));
    assert og_pc
       ==> elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (found <==> og_old_found);
    og_pc, og_ok := elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (found <==> found)
         && (!found
           ==> (forall second_ii: int :: 
            0 <= second_ii && second_ii < max
               ==> !(old_valid[second_ii] && old_elt[second_ii] == x)))
         && (found
           ==> (exists second_ii: int :: 
            0 <= second_ii
               && second_ii < max
               && og_global_old_valid[second_ii]
               && og_global_old_elt[second_ii] == x)));
    og_pc_anon5_LoopHead, og_ok_anon5_LoopHead := og_pc, og_ok;
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset, og_old_found := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset, found;
    goto anon5_LoopHead;

  anon00:
    assert og_pc
       || 
      (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (found <==> found)
         && (!found
           ==> (forall second_ii: int :: 
            0 <= second_ii && second_ii < max
               ==> !(old_valid[second_ii] && old_elt[second_ii] == x)))
         && (found
           ==> (exists second_ii: int :: 
            0 <= second_ii
               && second_ii < max
               && og_global_old_valid[second_ii]
               && og_global_old_elt[second_ii] == x)));
    assert og_pc
       ==> elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (found <==> og_old_found);
    og_pc, og_ok := elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (found <==> found)
         && (!found
           ==> (forall second_ii: int :: 
            0 <= second_ii && second_ii < max
               ==> !(old_valid[second_ii] && old_elt[second_ii] == x)))
         && (found
           ==> (exists second_ii: int :: 
            0 <= second_ii
               && second_ii < max
               && og_global_old_valid[second_ii]
               && og_global_old_elt[second_ii] == x)));
    call og_Yield12_2_YieldLookUp_2(old_valid, old_elt);
    assume og_pc || (tid != nil && tid != done && x != null);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset, og_old_found := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset, found;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    j := 0;
    goto anon09, CallToYieldProc;

  anon316:
    assert og_pc
       || 
      (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (found <==> found)
         && (!found
           ==> (forall second_ii: int :: 
            0 <= second_ii && second_ii < max
               ==> !(old_valid[second_ii] && old_elt[second_ii] == x)))
         && (found
           ==> (exists second_ii: int :: 
            0 <= second_ii
               && second_ii < max
               && og_global_old_valid[second_ii]
               && og_global_old_elt[second_ii] == x)));
    assert og_pc
       ==> elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (found <==> og_old_found);
    og_pc, og_ok := elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (found <==> found)
         && (!found
           ==> (forall second_ii: int :: 
            0 <= second_ii && second_ii < max
               ==> !(old_valid[second_ii] && old_elt[second_ii] == x)))
         && (found
           ==> (exists second_ii: int :: 
            0 <= second_ii
               && second_ii < max
               && og_global_old_valid[second_ii]
               && og_global_old_elt[second_ii] == x)));
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset, og_old_found := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset, found;
    goto anon5_LoopHead;

  anon37:
    assert og_pc
       || 
      (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (found <==> found)
         && (!found
           ==> (forall second_ii: int :: 
            0 <= second_ii && second_ii < max
               ==> !(old_valid[second_ii] && old_elt[second_ii] == x)))
         && (found
           ==> (exists second_ii: int :: 
            0 <= second_ii
               && second_ii < max
               && og_global_old_valid[second_ii]
               && og_global_old_elt[second_ii] == x)));
    assert og_pc
       ==> elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (found <==> og_old_found);
    og_pc, og_ok := elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (found <==> found)
         && (!found
           ==> (forall second_ii: int :: 
            0 <= second_ii && second_ii < max
               ==> !(old_valid[second_ii] && old_elt[second_ii] == x)))
         && (found
           ==> (exists second_ii: int :: 
            0 <= second_ii
               && second_ii < max
               && og_global_old_valid[second_ii]
               && og_global_old_elt[second_ii] == x)));
    call og_Yield12_2_YieldLookUp_2(old_valid, old_elt);
    assume og_pc || (tid != nil && tid != done && x != null);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset, og_old_found := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset, found;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    j := j + 1;
    goto anon316, CallToYieldProc;

  anon6_Then17:
    assert og_pc
       || 
      (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (found <==> found)
         && (!found
           ==> (forall second_ii: int :: 
            0 <= second_ii && second_ii < max
               ==> !(old_valid[second_ii] && old_elt[second_ii] == x)))
         && (found
           ==> (exists second_ii: int :: 
            0 <= second_ii
               && second_ii < max
               && og_global_old_valid[second_ii]
               && og_global_old_elt[second_ii] == x)));
    assert og_pc
       ==> elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (found <==> og_old_found);
    og_pc, og_ok := elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (found <==> found)
         && (!found
           ==> (forall second_ii: int :: 
            0 <= second_ii && second_ii < max
               ==> !(old_valid[second_ii] && old_elt[second_ii] == x)))
         && (found
           ==> (exists second_ii: int :: 
            0 <= second_ii
               && second_ii < max
               && og_global_old_valid[second_ii]
               && og_global_old_elt[second_ii] == x)));
    assert og_ok;
    return;

  anon6_Then9:
    assert og_pc
       || 
      (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (found <==> found)
         && (!found
           ==> (forall second_ii: int :: 
            0 <= second_ii && second_ii < max
               ==> !(old_valid[second_ii] && old_elt[second_ii] == x)))
         && (found
           ==> (exists second_ii: int :: 
            0 <= second_ii
               && second_ii < max
               && og_global_old_valid[second_ii]
               && og_global_old_elt[second_ii] == x)));
    assert og_pc
       ==> elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (found <==> og_old_found);
    og_pc, og_ok := elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (found <==> found)
         && (!found
           ==> (forall second_ii: int :: 
            0 <= second_ii && second_ii < max
               ==> !(old_valid[second_ii] && old_elt[second_ii] == x)))
         && (found
           ==> (exists second_ii: int :: 
            0 <= second_ii
               && second_ii < max
               && og_global_old_valid[second_ii]
               && og_global_old_elt[second_ii] == x)));
    call og_Yield12_2_YieldLookUp_2(old_valid, old_elt);
    assume og_pc || (tid != nil && tid != done && x != null);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset, og_old_found := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset, found;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon6_Then17, CallToYieldProc;

  anon49:
    assert og_pc
       || 
      (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (found <==> found)
         && (!found
           ==> (forall second_ii: int :: 
            0 <= second_ii && second_ii < max
               ==> !(old_valid[second_ii] && old_elt[second_ii] == x)))
         && (found
           ==> (exists second_ii: int :: 
            0 <= second_ii
               && second_ii < max
               && og_global_old_valid[second_ii]
               && og_global_old_elt[second_ii] == x)));
    assert og_pc
       ==> elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (found <==> og_old_found);
    og_pc, og_ok := elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (found <==> found)
         && (!found
           ==> (forall second_ii: int :: 
            0 <= second_ii && second_ii < max
               ==> !(old_valid[second_ii] && old_elt[second_ii] == x)))
         && (found
           ==> (exists second_ii: int :: 
            0 <= second_ii
               && second_ii < max
               && og_global_old_valid[second_ii]
               && og_global_old_elt[second_ii] == x)));
    assert og_ok;
    return;

  anon41:
    assert og_pc
       || 
      (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (found <==> found)
         && (!found
           ==> (forall second_ii: int :: 
            0 <= second_ii && second_ii < max
               ==> !(old_valid[second_ii] && old_elt[second_ii] == x)))
         && (found
           ==> (exists second_ii: int :: 
            0 <= second_ii
               && second_ii < max
               && og_global_old_valid[second_ii]
               && og_global_old_elt[second_ii] == x)));
    assert og_pc
       ==> elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (found <==> og_old_found);
    og_pc, og_ok := elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && (found <==> found)
         && (!found
           ==> (forall second_ii: int :: 
            0 <= second_ii && second_ii < max
               ==> !(old_valid[second_ii] && old_elt[second_ii] == x)))
         && (found
           ==> (exists second_ii: int :: 
            0 <= second_ii
               && second_ii < max
               && og_global_old_valid[second_ii]
               && og_global_old_elt[second_ii] == x)));
    call og_Yield12_2_YieldLookUp_2(old_valid, old_elt);
    assume og_pc || (tid != nil && tid != done && x != null);
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset, og_old_found := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), elt, valid, lock, owner, pendingAsyncMultiset, found;
    assume (exists partition_tid: [X]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon49, CallToYieldProc;

  CallToYieldProc:
    call og_yield_2(linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation Yield12_2()
{
  var og_global_old_elt: [int]int;
  var og_global_old_valid: [int]bool;
  var og_global_old_lock: [int]X;
  var og_global_old_owner: [int]X;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;
  var linear_tid_available: [X]bool;

  /*** structured program:
    yield;
    assert Inv(valid, elt, owner);
  **** end structured program */

  og_init:
    og_pc, og_ok, linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := false, false, linear_tid_MapConstBool(false), elt, valid, lock, owner, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assert Inv(valid, elt, owner);
    goto anon01, CallToYieldProc;

  anon09:
    assert og_pc
       || 
      (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_pc
       ==> elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_ok;
    return;

  anon01:
    assert og_pc
       || 
      (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_pc
       ==> elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    havoc elt, valid, lock, owner, pendingAsyncMultiset;
    assume true;
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapConstBool(false), elt, valid, lock, owner, pendingAsyncMultiset;
    assume Inv(valid, elt, owner);
    goto anon09, CallToYieldProc;

  CallToYieldProc:
    call og_yield_2(linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation YieldLookUp_2(old_valid: [int]bool, old_elt: [int]int)
{
  var og_global_old_elt: [int]int;
  var og_global_old_valid: [int]bool;
  var og_global_old_lock: [int]X;
  var og_global_old_owner: [int]X;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;
  var linear_tid_available: [X]bool;

  /*** structured program:
    yield;
    assert (forall ii: int :: 
      0 <= ii && ii < max && old_valid[ii] ==> valid[ii] && old_elt[ii] == elt[ii]);
  **** end structured program */

  og_init:
    og_pc, og_ok, linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := false, false, linear_tid_MapConstBool(false), elt, valid, lock, owner, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assert (forall ii: int :: 
      0 <= ii && ii < max && old_valid[ii] ==> valid[ii] && old_elt[ii] == elt[ii]);
    goto anon01, CallToYieldProc;

  anon09:
    assert og_pc
       || 
      (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_pc
       ==> elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_ok;
    return;

  anon01:
    assert og_pc
       || 
      (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_pc
       ==> elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (
        elt == og_global_old_elt
         && valid == og_global_old_valid
         && lock == og_global_old_lock
         && owner == og_global_old_owner
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    havoc elt, valid, lock, owner, pendingAsyncMultiset;
    assume true;
    linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset := linear_tid_MapConstBool(false), elt, valid, lock, owner, pendingAsyncMultiset;
    assume (forall ii: int :: 
      0 <= ii && ii < max && old_valid[ii] ==> valid[ii] && old_elt[ii] == elt[ii]);
    goto anon09, CallToYieldProc;

  CallToYieldProc:
    call og_yield_2(linear_tid_available, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



procedure {:inline 1} Impl_YieldChecker_Yield12_2(linear_tid_in: [X]bool, 
    og_global_old_elt: [int]int, 
    og_global_old_valid: [int]bool, 
    og_global_old_lock: [int]X, 
    og_global_old_owner: [int]X, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_YieldLookUp_2(linear_tid_in: [X]bool, 
    og_global_old_elt: [int]int, 
    og_global_old_valid: [int]bool, 
    og_global_old_lock: [int]X, 
    og_global_old_owner: [int]X, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



implementation {:inline 1} Impl_YieldChecker_Yield12_2(linear_tid_in: [X]bool, 
    og_global_old_elt: [int]int, 
    og_global_old_valid: [int]bool, 
    og_global_old_lock: [int]X, 
    og_global_old_owner: [int]X, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var og_local_old_elt: [int]int;
  var og_local_old_valid: [int]bool;
  var og_local_old_lock: [int]X;
  var og_local_old_owner: [int]X;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume Inv(og_global_old_valid, og_global_old_elt, og_global_old_owner);
    assert Inv(valid, elt, owner);
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_YieldLookUp_2(linear_tid_in: [X]bool, 
    og_global_old_elt: [int]int, 
    og_global_old_valid: [int]bool, 
    og_global_old_lock: [int]X, 
    og_global_old_owner: [int]X, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var old_valid: [int]bool;
  var old_elt: [int]int;
  var og_local_old_elt: [int]int;
  var og_local_old_valid: [int]bool;
  var og_local_old_lock: [int]X;
  var og_local_old_owner: [int]X;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (forall ii: int :: 
      0 <= ii && ii < max && old_valid[ii]
         ==> og_global_old_valid[ii] && old_elt[ii] == og_global_old_elt[ii]);
    assert (forall ii: int :: 
      0 <= ii && ii < max && old_valid[ii] ==> valid[ii] && old_elt[ii] == elt[ii]);
    assume false;
    return;
}



procedure og_Yield12_2();
  requires Inv(valid, elt, owner);
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures Inv(valid, elt, owner);



procedure og_Yield12_2_YieldLookUp_2(og_1_old_valid: [int]bool, og_1_old_elt: [int]int);
  requires Inv(valid, elt, owner);
  requires (forall ii: int :: 
    0 <= ii && ii < max && og_1_old_valid[ii]
       ==> valid[ii] && og_1_old_elt[ii] == elt[ii]);
  modifies elt, valid, lock, owner, pendingAsyncMultiset;
  ensures Inv(valid, elt, owner);
  ensures (forall ii: int :: 
    0 <= ii && ii < max && og_1_old_valid[ii]
       ==> valid[ii] && og_1_old_elt[ii] == elt[ii]);



procedure {:inline 1} og_yield_2(linear_tid_in: [X]bool, 
    og_global_old_elt: [int]int, 
    og_global_old_valid: [int]bool, 
    og_global_old_lock: [int]X, 
    og_global_old_owner: [int]X, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



implementation {:inline 1} og_yield_2(linear_tid_in: [X]bool, 
    og_global_old_elt: [int]int, 
    og_global_old_valid: [int]bool, 
    og_global_old_lock: [int]X, 
    og_global_old_owner: [int]X, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{

  enter:
    goto L_0, L_1;

  L_0:
    call Impl_YieldChecker_Yield12_2(linear_tid_in, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset);
    return;

  L_1:
    call Impl_YieldChecker_YieldLookUp_2(linear_tid_in, og_global_old_elt, og_global_old_valid, og_global_old_lock, og_global_old_owner, og_global_old_pendingAsyncMultiset);
    return;
}


