// Boogie program verifier version 2.4.1.10503, Copyright (c) 2003-2014, Microsoft.
// Command Line Options: /noWitnessInference /noCommutativityTriggers /noVerify /CivlDesugaredFile:desugared_files/array-insert.desugared.bpl ../array-insert.bpl

type Tid;

const nil: Tid;

var A: [int]int;

var count: int;

var lock: Tid;

function {:inline 1} sorted(A: [int]int, count: int) : bool;

axiom (forall A: [int]int, count: int :: 
  {:inline 1} { sorted(A, count): bool } 
  sorted(A, count): bool
     <==> (forall i: int, j: int :: 0 <= i && i <= j && j < count ==> A[i] <= A[j]));

procedure {:inline 1} snapshot() returns (snapshot: [int]int);



implementation {:inline 1} snapshot() returns (snapshot: [int]int)
{
  /*** structured program:
    snapshot := A;
  **** end structured program */

  anon0:
    snapshot := A;
    return;
}



function {:builtin "MapConst"} MapConstBool(bool) : [Tid]bool;

function {:inline} TidCollector(tid: Tid) : [Tid]bool
{
  MapConstBool(false)[tid := true]
}

type {:datatype} PendingAsync;

var pendingAsyncMultiset: [PendingAsync]int;

function {:constructor} PendingAsync_insert(tid: Tid, v: int) : PendingAsync;

procedure {:inline 1} AddPendingAsync_insert(tid: Tid, v: int);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_insert(tid: Tid, v: int)
{

  L:
    pendingAsyncMultiset[PendingAsync_insert(tid, v)] := pendingAsyncMultiset[PendingAsync_insert(tid, v)] + 1;
    return;
}



function {:constructor} PendingAsync_read_A(tid: Tid, i: int) : PendingAsync;

procedure {:inline 1} AddPendingAsync_read_A(tid: Tid, i: int);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_read_A(tid: Tid, i: int)
{

  L:
    pendingAsyncMultiset[PendingAsync_read_A(tid, i)] := pendingAsyncMultiset[PendingAsync_read_A(tid, i)] + 1;
    return;
}



function {:constructor} PendingAsync_write_A(tid: Tid, i: int, v: int) : PendingAsync;

procedure {:inline 1} AddPendingAsync_write_A(tid: Tid, i: int, v: int);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_write_A(tid: Tid, i: int, v: int)
{

  L:
    pendingAsyncMultiset[PendingAsync_write_A(tid, i, v)] := pendingAsyncMultiset[PendingAsync_write_A(tid, i, v)] + 1;
    return;
}



function {:constructor} PendingAsync_read_count(tid: Tid) : PendingAsync;

procedure {:inline 1} AddPendingAsync_read_count(tid: Tid);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_read_count(tid: Tid)
{

  L:
    pendingAsyncMultiset[PendingAsync_read_count(tid)] := pendingAsyncMultiset[PendingAsync_read_count(tid)] + 1;
    return;
}



function {:constructor} PendingAsync_write_count(tid: Tid, c: int) : PendingAsync;

procedure {:inline 1} AddPendingAsync_write_count(tid: Tid, c: int);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_write_count(tid: Tid, c: int)
{

  L:
    pendingAsyncMultiset[PendingAsync_write_count(tid, c)] := pendingAsyncMultiset[PendingAsync_write_count(tid, c)] + 1;
    return;
}



function {:constructor} PendingAsync_acquire(tid: Tid) : PendingAsync;

procedure {:inline 1} AddPendingAsync_acquire(tid: Tid);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_acquire(tid: Tid)
{

  L:
    pendingAsyncMultiset[PendingAsync_acquire(tid)] := pendingAsyncMultiset[PendingAsync_acquire(tid)] + 1;
    return;
}



function {:constructor} PendingAsync_release(tid: Tid) : PendingAsync;

procedure {:inline 1} AddPendingAsync_release(tid: Tid);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_release(tid: Tid)
{

  L:
    pendingAsyncMultiset[PendingAsync_release(tid)] := pendingAsyncMultiset[PendingAsync_release(tid)] + 1;
    return;
}



procedure {:inline 1} READ_A_1(tid: Tid, i: int) returns (v: int);



procedure {:inline 1} WRITE_A_1(tid: Tid, i: int, v: int);
  modifies A;



procedure {:inline 1} READ_COUNT_1(tid: Tid) returns (c: int);



procedure {:inline 1} WRITE_COUNT_1(tid: Tid, c: int);
  modifies count;



procedure {:inline 1} ACQUIRE_1(tid: Tid);
  modifies lock;



procedure {:inline 1} RELEASE_1(tid: Tid);
  modifies lock;



implementation {:inline 1} READ_A_1(tid: Tid, i: int) returns (v: int)
{
  /*** structured program:
    assert tid != nil && lock == tid;
    v := A[i];
  **** end structured program */

  anon0:
    v := A[i];
    return;
}



implementation {:inline 1} WRITE_A_1(tid: Tid, i: int, v: int)
{
  /*** structured program:
    assert tid != nil && lock == tid;
    A[i] := v;
  **** end structured program */

  anon0:
    A[i] := v;
    return;
}



implementation {:inline 1} READ_COUNT_1(tid: Tid) returns (c: int)
{
  /*** structured program:
    assert tid != nil && lock == tid;
    c := count;
  **** end structured program */

  anon0:
    c := count;
    return;
}



implementation {:inline 1} WRITE_COUNT_1(tid: Tid, c: int)
{
  /*** structured program:
    assert tid != nil && lock == tid;
    count := c;
  **** end structured program */

  anon0:
    count := c;
    return;
}



implementation {:inline 1} ACQUIRE_1(tid: Tid)
{
  /*** structured program:
    assert tid != nil;
    assume lock == nil;
    lock := tid;
  **** end structured program */

  anon0:
    assume lock == nil;
    lock := tid;
    return;
}



implementation {:inline 1} RELEASE_1(tid: Tid)
{
  /*** structured program:
    assert tid != nil && lock == tid;
    lock := nil;
  **** end structured program */

  anon0:
    lock := nil;
    return;
}



procedure {:inline 1} INSERT_2(tid: Tid, v: int);
  modifies A, count;



implementation {:inline 1} INSERT_2(tid: Tid, v: int)
{
  var idx: int;
  var A_new: [int]int;

  /*** structured program:
    assert count >= 0;
    assert sorted(A, count);
    assume 0 <= idx && idx <= count;
    assume (forall i: int :: 0 <= i && i < idx ==> A[i] < v);
    assume (forall i: int :: idx <= i && i < count ==> A[i] >= v);
    assume (forall i: int :: i < idx ==> A_new[i] == A[i]);
    assume (forall i: int :: idx < i && i < count ==> A_new[i + 1] == A[i]);
    assume (forall i: int :: count < i ==> A_new[i] == A[i]);
    A_new[idx] := v;
    A := A_new;
    count := count + 1;
  **** end structured program */

  anon0:
    assume 0 <= idx && idx <= count;
    assume (forall i: int :: 0 <= i && i < idx ==> A[i] < v);
    assume (forall i: int :: idx <= i && i < count ==> A[i] >= v);
    assume (forall i: int :: i < idx ==> A_new[i] == A[i]);
    assume (forall i: int :: idx < i && i < count ==> A_new[i + 1] == A[i]);
    assume (forall i: int :: count < i ==> A_new[i] == A[i]);
    A_new[idx] := v;
    A := A_new;
    count := count + 1;
    return;
}



var linear_tid_hole: [Tid]bool;

function linear_tid_MapConstBool(b: bool) : [Tid]bool;

function linear_tid_MapConstInt(b: int) : [Tid]int;

function linear_tid_MapEq(a: [Tid]int, b: [Tid]int) : [Tid]bool;

function linear_tid_MapImp(a: [Tid]bool, b: [Tid]bool) : [Tid]bool;

function linear_tid_MapOr(a: [Tid]bool, b: [Tid]bool) : [Tid]bool;

axiom (forall a: [Tid]bool, b: [Tid]bool :: 
  { linear_tid_MapOr(a, b) } 
  (forall x: Tid :: linear_tid_MapOr(a, b)[x] <==> a[x] || b[x]));

axiom (forall a: [Tid]bool, b: [Tid]bool :: 
  { linear_tid_MapImp(a, b) } 
  (forall x: Tid :: linear_tid_MapImp(a, b)[x] <==> a[x] ==> b[x]));

axiom (forall x: Tid :: linear_tid_MapConstBool(true)[x]);

axiom (forall x: Tid :: !linear_tid_MapConstBool(false)[x]);

axiom (forall a: [Tid]int, b: [Tid]int :: 
  { linear_tid_MapEq(a, b) } 
  (forall x: Tid :: linear_tid_MapEq(a, b)[x] <==> a[x] == b[x]));

axiom (forall a: int, x: Tid :: linear_tid_MapConstInt(a)[x] == a);

implementation CommutativityChecker_READ_A_1_WRITE_A_1(first_tid: Tid, first_i: int, second_tid: Tid, second_i: int, second_v: int)
   returns (first_v: int)
{

  first_anon0:
    first_v := A[first_i];
    goto second_anon0;

  second_anon0:
    A[second_i] := second_v;
    return;
}



procedure CommutativityChecker_READ_A_1_WRITE_A_1(first_tid: Tid, first_i: int, second_tid: Tid, second_i: int, second_v: int)
   returns (first_v: int);
  requires (exists partition_tid: [Tid]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires first_tid != nil && lock == first_tid;
  requires second_tid != nil && lock == second_tid;
  modifies A, count, lock, pendingAsyncMultiset;
  ensures true
     ==> lock == old(lock)
       && A == old(A)[second_i := second_v]
       && first_v == old(A)[second_i := second_v][first_i];



implementation CommutativityChecker_WRITE_A_1_READ_A_1(first_tid: Tid, first_i: int, first_v: int, second_tid: Tid, second_i: int)
   returns (second_v: int)
{

  first_anon0:
    A[first_i] := first_v;
    goto second_anon0;

  second_anon0:
    second_v := A[second_i];
    return;
}



procedure CommutativityChecker_WRITE_A_1_READ_A_1(first_tid: Tid, first_i: int, first_v: int, second_tid: Tid, second_i: int)
   returns (second_v: int);
  requires (exists partition_tid: [Tid]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires first_tid != nil && lock == first_tid;
  requires second_tid != nil && lock == second_tid;
  modifies A, count, lock, pendingAsyncMultiset;
  ensures true
     ==> lock == old(lock)
       && A == old(A)[first_i := first_v]
       && second_v == old(A)[second_i];



implementation GatePreservationChecker_READ_A_1_ACQUIRE_1(first_tid: Tid, first_i: int, second_tid: Tid) returns (first_v: int)
{

  second_anon0:
    assume lock == nil;
    lock := second_tid;
    return;
}



procedure GatePreservationChecker_READ_A_1_ACQUIRE_1(first_tid: Tid, first_i: int, second_tid: Tid) returns (first_v: int);
  requires (exists partition_tid: [Tid]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires second_tid != nil;
  requires first_tid != nil && lock == first_tid;
  modifies A, count, lock, pendingAsyncMultiset;
  ensures true ==> first_tid != nil && lock == first_tid;



implementation GatePreservationChecker_READ_A_1_RELEASE_1(first_tid: Tid, first_i: int, second_tid: Tid) returns (first_v: int)
{

  second_anon0:
    lock := nil;
    return;
}



procedure GatePreservationChecker_READ_A_1_RELEASE_1(first_tid: Tid, first_i: int, second_tid: Tid) returns (first_v: int);
  requires (exists partition_tid: [Tid]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires second_tid != nil && lock == second_tid;
  requires first_tid != nil && lock == first_tid;
  modifies A, count, lock, pendingAsyncMultiset;
  ensures true ==> first_tid != nil && lock == first_tid;



implementation CommutativityChecker_WRITE_A_1_WRITE_A_1(first_tid: Tid, 
    first_i: int, 
    first_v: int, 
    second_tid: Tid, 
    second_i: int, 
    second_v: int)
{

  first_anon0:
    A[first_i] := first_v;
    goto second_anon0;

  second_anon0:
    A[second_i] := second_v;
    return;
}



procedure CommutativityChecker_WRITE_A_1_WRITE_A_1(first_tid: Tid, 
    first_i: int, 
    first_v: int, 
    second_tid: Tid, 
    second_i: int, 
    second_v: int);
  requires (exists partition_tid: [Tid]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires first_tid != nil && lock == first_tid;
  requires second_tid != nil && lock == second_tid;
  modifies A, count, lock, pendingAsyncMultiset;
  ensures true
     ==> lock == old(lock) && A == old(A)[second_i := second_v][first_i := first_v];



implementation GatePreservationChecker_WRITE_A_1_ACQUIRE_1(first_tid: Tid, first_i: int, first_v: int, second_tid: Tid)
{

  second_anon0:
    assume lock == nil;
    lock := second_tid;
    return;
}



procedure GatePreservationChecker_WRITE_A_1_ACQUIRE_1(first_tid: Tid, first_i: int, first_v: int, second_tid: Tid);
  requires (exists partition_tid: [Tid]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires second_tid != nil;
  requires first_tid != nil && lock == first_tid;
  modifies A, count, lock, pendingAsyncMultiset;
  ensures true ==> first_tid != nil && lock == first_tid;



implementation GatePreservationChecker_WRITE_A_1_RELEASE_1(first_tid: Tid, first_i: int, first_v: int, second_tid: Tid)
{

  second_anon0:
    lock := nil;
    return;
}



procedure GatePreservationChecker_WRITE_A_1_RELEASE_1(first_tid: Tid, first_i: int, first_v: int, second_tid: Tid);
  requires (exists partition_tid: [Tid]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires second_tid != nil && lock == second_tid;
  requires first_tid != nil && lock == first_tid;
  modifies A, count, lock, pendingAsyncMultiset;
  ensures true ==> first_tid != nil && lock == first_tid;



implementation CommutativityChecker_READ_COUNT_1_WRITE_COUNT_1(first_tid: Tid, second_tid: Tid, second_c: int) returns (first_c: int)
{

  first_anon0:
    first_c := count;
    goto second_anon0;

  second_anon0:
    count := second_c;
    return;
}



procedure CommutativityChecker_READ_COUNT_1_WRITE_COUNT_1(first_tid: Tid, second_tid: Tid, second_c: int) returns (first_c: int);
  requires (exists partition_tid: [Tid]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires first_tid != nil && lock == first_tid;
  requires second_tid != nil && lock == second_tid;
  modifies A, count, lock, pendingAsyncMultiset;
  ensures true ==> lock == old(lock) && count == second_c && first_c == second_c;



implementation CommutativityChecker_WRITE_COUNT_1_READ_COUNT_1(first_tid: Tid, first_c: int, second_tid: Tid) returns (second_c: int)
{

  first_anon0:
    count := first_c;
    goto second_anon0;

  second_anon0:
    second_c := count;
    return;
}



procedure CommutativityChecker_WRITE_COUNT_1_READ_COUNT_1(first_tid: Tid, first_c: int, second_tid: Tid) returns (second_c: int);
  requires (exists partition_tid: [Tid]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires first_tid != nil && lock == first_tid;
  requires second_tid != nil && lock == second_tid;
  modifies A, count, lock, pendingAsyncMultiset;
  ensures true ==> lock == old(lock) && count == first_c && second_c == old(count);



implementation GatePreservationChecker_READ_COUNT_1_ACQUIRE_1(first_tid: Tid, second_tid: Tid) returns (first_c: int)
{

  second_anon0:
    assume lock == nil;
    lock := second_tid;
    return;
}



procedure GatePreservationChecker_READ_COUNT_1_ACQUIRE_1(first_tid: Tid, second_tid: Tid) returns (first_c: int);
  requires (exists partition_tid: [Tid]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires second_tid != nil;
  requires first_tid != nil && lock == first_tid;
  modifies A, count, lock, pendingAsyncMultiset;
  ensures true ==> first_tid != nil && lock == first_tid;



implementation GatePreservationChecker_READ_COUNT_1_RELEASE_1(first_tid: Tid, second_tid: Tid) returns (first_c: int)
{

  second_anon0:
    lock := nil;
    return;
}



procedure GatePreservationChecker_READ_COUNT_1_RELEASE_1(first_tid: Tid, second_tid: Tid) returns (first_c: int);
  requires (exists partition_tid: [Tid]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires second_tid != nil && lock == second_tid;
  requires first_tid != nil && lock == first_tid;
  modifies A, count, lock, pendingAsyncMultiset;
  ensures true ==> first_tid != nil && lock == first_tid;



implementation CommutativityChecker_WRITE_COUNT_1_WRITE_COUNT_1(first_tid: Tid, first_c: int, second_tid: Tid, second_c: int)
{

  first_anon0:
    count := first_c;
    goto second_anon0;

  second_anon0:
    count := second_c;
    return;
}



procedure CommutativityChecker_WRITE_COUNT_1_WRITE_COUNT_1(first_tid: Tid, first_c: int, second_tid: Tid, second_c: int);
  requires (exists partition_tid: [Tid]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires first_tid != nil && lock == first_tid;
  requires second_tid != nil && lock == second_tid;
  modifies A, count, lock, pendingAsyncMultiset;
  ensures true ==> lock == old(lock) && count == first_c;



implementation GatePreservationChecker_WRITE_COUNT_1_ACQUIRE_1(first_tid: Tid, first_c: int, second_tid: Tid)
{

  second_anon0:
    assume lock == nil;
    lock := second_tid;
    return;
}



procedure GatePreservationChecker_WRITE_COUNT_1_ACQUIRE_1(first_tid: Tid, first_c: int, second_tid: Tid);
  requires (exists partition_tid: [Tid]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires second_tid != nil;
  requires first_tid != nil && lock == first_tid;
  modifies A, count, lock, pendingAsyncMultiset;
  ensures true ==> first_tid != nil && lock == first_tid;



implementation GatePreservationChecker_WRITE_COUNT_1_RELEASE_1(first_tid: Tid, first_c: int, second_tid: Tid)
{

  second_anon0:
    lock := nil;
    return;
}



procedure GatePreservationChecker_WRITE_COUNT_1_RELEASE_1(first_tid: Tid, first_c: int, second_tid: Tid);
  requires (exists partition_tid: [Tid]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires second_tid != nil && lock == second_tid;
  requires first_tid != nil && lock == first_tid;
  modifies A, count, lock, pendingAsyncMultiset;
  ensures true ==> first_tid != nil && lock == first_tid;



implementation CommutativityChecker_ACQUIRE_1_ACQUIRE_1(first_tid: Tid, second_tid: Tid)
{

  first_anon0:
    assume lock == nil;
    lock := first_tid;
    goto second_anon0;

  second_anon0:
    assume lock == nil;
    lock := second_tid;
    return;
}



procedure CommutativityChecker_ACQUIRE_1_ACQUIRE_1(first_tid: Tid, second_tid: Tid);
  requires (exists partition_tid: [Tid]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires first_tid != nil;
  requires second_tid != nil;
  modifies A, count, lock, pendingAsyncMultiset;
  ensures true ==> lock == first_tid && second_tid == nil && old(lock) == nil;



implementation CommutativityChecker_ACQUIRE_1_RELEASE_1(first_tid: Tid, second_tid: Tid)
{

  first_anon0:
    assume lock == nil;
    lock := first_tid;
    goto second_anon0;

  second_anon0:
    lock := nil;
    return;
}



procedure CommutativityChecker_ACQUIRE_1_RELEASE_1(first_tid: Tid, second_tid: Tid);
  requires (exists partition_tid: [Tid]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires first_tid != nil;
  requires second_tid != nil && lock == second_tid;
  modifies A, count, lock, pendingAsyncMultiset;
  ensures true ==> lock == first_tid && nil == nil;



implementation GatePreservationChecker_RELEASE_1_ACQUIRE_1(first_tid: Tid, second_tid: Tid)
{

  second_anon0:
    assume lock == nil;
    lock := second_tid;
    return;
}



procedure GatePreservationChecker_RELEASE_1_ACQUIRE_1(first_tid: Tid, second_tid: Tid);
  requires (exists partition_tid: [Tid]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires second_tid != nil;
  requires first_tid != nil && lock == first_tid;
  modifies A, count, lock, pendingAsyncMultiset;
  ensures true ==> first_tid != nil && lock == first_tid;



implementation FailurePreservationChecker_READ_A_1_RELEASE_1(first_tid: Tid, first_i: int, second_tid: Tid) returns (first_v: int)
{

  second_anon0:
    lock := nil;
    return;
}



procedure FailurePreservationChecker_READ_A_1_RELEASE_1(first_tid: Tid, first_i: int, second_tid: Tid) returns (first_v: int);
  requires (exists partition_tid: [Tid]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires !(first_tid != nil && lock == first_tid);
  requires second_tid != nil && lock == second_tid;
  modifies A, count, lock, pendingAsyncMultiset;
  ensures true ==> !(first_tid != nil && lock == first_tid);



implementation FailurePreservationChecker_WRITE_A_1_RELEASE_1(first_tid: Tid, first_i: int, first_v: int, second_tid: Tid)
{

  second_anon0:
    lock := nil;
    return;
}



procedure FailurePreservationChecker_WRITE_A_1_RELEASE_1(first_tid: Tid, first_i: int, first_v: int, second_tid: Tid);
  requires (exists partition_tid: [Tid]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires !(first_tid != nil && lock == first_tid);
  requires second_tid != nil && lock == second_tid;
  modifies A, count, lock, pendingAsyncMultiset;
  ensures true ==> !(first_tid != nil && lock == first_tid);



implementation FailurePreservationChecker_READ_COUNT_1_RELEASE_1(first_tid: Tid, second_tid: Tid) returns (first_c: int)
{

  second_anon0:
    lock := nil;
    return;
}



procedure FailurePreservationChecker_READ_COUNT_1_RELEASE_1(first_tid: Tid, second_tid: Tid) returns (first_c: int);
  requires (exists partition_tid: [Tid]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires !(first_tid != nil && lock == first_tid);
  requires second_tid != nil && lock == second_tid;
  modifies A, count, lock, pendingAsyncMultiset;
  ensures true ==> !(first_tid != nil && lock == first_tid);



implementation FailurePreservationChecker_WRITE_COUNT_1_RELEASE_1(first_tid: Tid, first_c: int, second_tid: Tid)
{

  second_anon0:
    lock := nil;
    return;
}



procedure FailurePreservationChecker_WRITE_COUNT_1_RELEASE_1(first_tid: Tid, first_c: int, second_tid: Tid);
  requires (exists partition_tid: [Tid]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires !(first_tid != nil && lock == first_tid);
  requires second_tid != nil && lock == second_tid;
  modifies A, count, lock, pendingAsyncMultiset;
  ensures true ==> !(first_tid != nil && lock == first_tid);



implementation CommutativityChecker_RELEASE_1_RELEASE_1(first_tid: Tid, second_tid: Tid)
{

  first_anon0:
    lock := nil;
    goto second_anon0;

  second_anon0:
    lock := nil;
    return;
}



procedure CommutativityChecker_RELEASE_1_RELEASE_1(first_tid: Tid, second_tid: Tid);
  requires (exists partition_tid: [Tid]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires first_tid != nil && lock == first_tid;
  requires second_tid != nil && lock == second_tid;
  modifies A, count, lock, pendingAsyncMultiset;
  ensures true ==> lock == nil;



implementation GatePreservationChecker_RELEASE_1_RELEASE_1(first_tid: Tid, second_tid: Tid)
{

  second_anon0:
    lock := nil;
    return;
}



procedure GatePreservationChecker_RELEASE_1_RELEASE_1(first_tid: Tid, second_tid: Tid);
  requires (exists partition_tid: [Tid]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires second_tid != nil && lock == second_tid;
  requires first_tid != nil && lock == first_tid;
  modifies A, count, lock, pendingAsyncMultiset;
  ensures true ==> first_tid != nil && lock == first_tid;



implementation FailurePreservationChecker_RELEASE_1_RELEASE_1(first_tid: Tid, second_tid: Tid)
{

  second_anon0:
    lock := nil;
    return;
}



procedure FailurePreservationChecker_RELEASE_1_RELEASE_1(first_tid: Tid, second_tid: Tid);
  requires (exists partition_tid: [Tid]int :: 
    linear_tid_MapImp(TidCollector(first_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
         == linear_tid_MapConstBool(true)
       && linear_tid_MapImp(TidCollector(second_tid), 
          linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
         == linear_tid_MapConstBool(true));
  requires !(first_tid != nil && lock == first_tid);
  requires second_tid != nil && lock == second_tid;
  modifies A, count, lock, pendingAsyncMultiset;
  ensures true ==> !(first_tid != nil && lock == first_tid);



procedure insert_0(tid: Tid, v: int);
  modifies A, count, lock, pendingAsyncMultiset;



procedure read_A_0(tid: Tid, i: int) returns (v: int);
  modifies A, count, lock, pendingAsyncMultiset;



procedure write_A_0(tid: Tid, i: int, v: int);
  modifies A, count, lock, pendingAsyncMultiset;



procedure read_count_0(tid: Tid) returns (c: int);
  modifies A, count, lock, pendingAsyncMultiset;



procedure write_count_0(tid: Tid, c: int);
  modifies A, count, lock, pendingAsyncMultiset;



procedure acquire_0(tid: Tid);
  modifies A, count, lock, pendingAsyncMultiset;



procedure release_0(tid: Tid);
  modifies A, count, lock, pendingAsyncMultiset;



implementation insert_0(tid: Tid, v: int)
{
  var idx: int;
  var j: int;
  var a: int;
  var c: int;
  var _A: [int]int;
  var og_global_old_A: [int]int;
  var og_global_old_count: int;
  var og_global_old_lock: Tid;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_tid_available: [Tid]bool;

  /*** structured program:
    yield;
    assert tid != nil;
    call _A := snapshot();
    call acquire(tid);
    idx := 0;
    call c := read_count(tid);
    call a := read_A(tid, idx);
    while (idx < c && a < v)
      invariant 0 <= idx && idx <= count;
      invariant a == A[idx];
      invariant (forall i: int :: 0 <= i && i < idx ==> A[i] < v);
    {
        idx := idx + 1;
        call a := read_A(tid, idx);
    }

    j := c;
    while (idx < j)
      invariant idx <= j && j <= count;
      invariant (forall i: int :: i <= j ==> A[i] == _A[i]);
      invariant (forall i: int :: j < i && i <= count ==> A[i] == _A[i - 1]);
      invariant (forall i: int :: count < i ==> A[i] == _A[i]);
    {
        call a := read_A(tid, j - 1);
        call write_A(tid, j, a);
        j := j - 1;
    }

    call write_A(tid, idx, v);
    call write_count(tid, c + 1);
    assert sorted(A, count);
    call release(tid);
    yield;
  **** end structured program */

  og_init:
    linear_tid_available, og_global_old_A, og_global_old_count, og_global_old_lock, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), A, count, lock, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon02, CallToYieldProc;

  anon5_LoopHead:
    assume linear_tid_available
       == linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false));
    assume A == og_global_old_A;
    assume count == og_global_old_count;
    assume lock == og_global_old_lock;
    assume pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon5_LoopDone, anon5_LoopBody;

  anon5_LoopBody:
    assume {:partition} idx < c && a < v;
    idx := idx + 1;
    goto anon5_LoopBody2, CallToYieldProc;

  anon5_LoopDone:
    assume {:partition} !(idx < c && a < v);
    goto anon2;

  anon2:
    j := c;
    goto anon21, CallToYieldProc;

  anon6_LoopHead:
    assume linear_tid_available
       == linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false));
    assume A == og_global_old_A;
    assume count == og_global_old_count;
    assume lock == og_global_old_lock;
    assume pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon6_LoopDone, anon6_LoopBody;

  anon6_LoopBody:
    assume {:partition} idx < j;
    goto anon6_LoopBody1, CallToYieldProc;

  anon6_LoopDone:
    assume {:partition} j <= idx;
    goto anon4;

  anon4:
    goto anon40, CallToYieldProc;

  anon020:
    linear_tid_available, og_global_old_A, og_global_old_count, og_global_old_lock, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), A, count, lock, pendingAsyncMultiset;
    goto anon5_LoopHead;

  anon016:
    call a := read_A_0(tid, idx);
    linear_tid_available, og_global_old_A, og_global_old_count, og_global_old_lock, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), A, count, lock, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon020, CallToYieldProc;

  anon012:
    call c := read_count_0(tid);
    linear_tid_available, og_global_old_A, og_global_old_count, og_global_old_lock, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), A, count, lock, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon016, CallToYieldProc;

  anon07:
    call acquire_0(tid);
    linear_tid_available, og_global_old_A, og_global_old_count, og_global_old_lock, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), A, count, lock, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    idx := 0;
    goto anon012, CallToYieldProc;

  anon02:
    havoc A, count, lock, pendingAsyncMultiset;
    linear_tid_available, og_global_old_A, og_global_old_count, og_global_old_lock, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), A, count, lock, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon07, CallToYieldProc;

  anon5_LoopBody6:
    linear_tid_available, og_global_old_A, og_global_old_count, og_global_old_lock, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), A, count, lock, pendingAsyncMultiset;
    goto anon5_LoopHead;

  anon5_LoopBody2:
    call a := read_A_0(tid, idx);
    linear_tid_available, og_global_old_A, og_global_old_count, og_global_old_lock, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), A, count, lock, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon5_LoopBody6, CallToYieldProc;

  anon21:
    linear_tid_available, og_global_old_A, og_global_old_count, og_global_old_lock, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), A, count, lock, pendingAsyncMultiset;
    goto anon6_LoopHead;

  anon6_LoopBody10:
    linear_tid_available, og_global_old_A, og_global_old_count, og_global_old_lock, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), A, count, lock, pendingAsyncMultiset;
    goto anon6_LoopHead;

  anon6_LoopBody5:
    call write_A_0(tid, j, a);
    linear_tid_available, og_global_old_A, og_global_old_count, og_global_old_lock, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), A, count, lock, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    j := j - 1;
    goto anon6_LoopBody10, CallToYieldProc;

  anon6_LoopBody1:
    call a := read_A_0(tid, j - 1);
    linear_tid_available, og_global_old_A, og_global_old_count, og_global_old_lock, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), A, count, lock, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon6_LoopBody5, CallToYieldProc;

  anon417:
    return;

  anon413:
    havoc A, count, lock, pendingAsyncMultiset;
    linear_tid_available, og_global_old_A, og_global_old_count, og_global_old_lock, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), A, count, lock, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon417, CallToYieldProc;

  anon48:
    call release_0(tid);
    linear_tid_available, og_global_old_A, og_global_old_count, og_global_old_lock, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), A, count, lock, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon413, CallToYieldProc;

  anon44:
    call write_count_0(tid, c + 1);
    linear_tid_available, og_global_old_A, og_global_old_count, og_global_old_lock, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), A, count, lock, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon48, CallToYieldProc;

  anon40:
    call write_A_0(tid, idx, v);
    linear_tid_available, og_global_old_A, og_global_old_count, og_global_old_lock, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), A, count, lock, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon44, CallToYieldProc;

  CallToYieldProc:
    call og_yield_0(linear_tid_available, og_global_old_A, og_global_old_count, og_global_old_lock, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



procedure {:inline 1} Impl_YieldChecker_insert_0(linear_tid_in: [Tid]bool, 
    og_global_old_A: [int]int, 
    og_global_old_count: int, 
    og_global_old_lock: Tid, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



implementation {:inline 1} Impl_YieldChecker_insert_0(linear_tid_in: [Tid]bool, 
    og_global_old_A: [int]int, 
    og_global_old_count: int, 
    og_global_old_lock: Tid, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var idx: int;
  var j: int;
  var a: int;
  var c: int;
  var _A: [int]int;
  var tid: Tid;
  var v: int;
  var og_local_old_A: [int]int;
  var og_local_old_count: int;
  var og_local_old_lock: Tid;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0, L1;

  exit:
    return;

  L0:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume false;
    return;

  L1:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume false;
    return;
}



procedure {:inline 1} og_yield_0(linear_tid_in: [Tid]bool, 
    og_global_old_A: [int]int, 
    og_global_old_count: int, 
    og_global_old_lock: Tid, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



implementation {:inline 1} og_yield_0(linear_tid_in: [Tid]bool, 
    og_global_old_A: [int]int, 
    og_global_old_count: int, 
    og_global_old_lock: Tid, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{

  enter:
    goto L_0;

  L_0:
    call Impl_YieldChecker_insert_0(linear_tid_in, og_global_old_A, og_global_old_count, og_global_old_lock, og_global_old_pendingAsyncMultiset);
    return;
}



procedure insert_1(tid: Tid, v: int);
  requires tid != nil;
  modifies A, count, lock, pendingAsyncMultiset;



implementation insert_1(tid: Tid, v: int)
{
  var idx: int;
  var j: int;
  var a: int;
  var c: int;
  var _A: [int]int;
  var og_global_old_A: [int]int;
  var og_global_old_count: int;
  var og_global_old_lock: Tid;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;
  var linear_tid_available: [Tid]bool;

  /*** structured program:
    yield;
    assert tid != nil;
    call _A := snapshot();
    call acquire(tid);
    idx := 0;
    call c := read_count(tid);
    call a := read_A(tid, idx);
    while (idx < c && a < v)
      invariant 0 <= idx && idx <= count;
      invariant a == A[idx];
      invariant (forall i: int :: 0 <= i && i < idx ==> A[i] < v);
    {
        idx := idx + 1;
        call a := read_A(tid, idx);
    }

    j := c;
    while (idx < j)
      invariant idx <= j && j <= count;
      invariant (forall i: int :: i <= j ==> A[i] == _A[i]);
      invariant (forall i: int :: j < i && i <= count ==> A[i] == _A[i - 1]);
      invariant (forall i: int :: count < i ==> A[i] == _A[i]);
    {
        call a := read_A(tid, j - 1);
        call write_A(tid, j, a);
        j := j - 1;
    }

    call write_A(tid, idx, v);
    call write_count(tid, c + 1);
    assert sorted(A, count);
    call release(tid);
    yield;
  **** end structured program */

  og_init:
    og_pc, og_ok, linear_tid_available, og_global_old_A, og_global_old_count, og_global_old_lock, og_global_old_pendingAsyncMultiset := false, false, linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), A, count, lock, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assert tid != nil;
    goto anon02, CallToYieldProc;

  anon5_LoopHead:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assert 0 <= idx && idx <= count;
    assert a == A[idx];
    assert (forall i: int :: 0 <= i && i < idx ==> A[i] < v);
    goto anon5_LoopDone, anon5_LoopBody;

  anon5_LoopBody:
    assume {:partition} idx < c && a < v;
    idx := idx + 1;
    // <<< injected gate
    assert tid != nil && lock == tid;
    // injected gate >>>
    call a := READ_A_1(tid, idx);
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon5_LoopHead;

  anon5_LoopDone:
    assume {:partition} !(idx < c && a < v);
    goto anon2;

  anon2:
    j := c;
    goto anon6_LoopHead;

  anon6_LoopHead:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assert idx <= j && j <= count;
    assert (forall i: int :: i <= j ==> A[i] == _A[i]);
    assert (forall i: int :: j < i && i <= count ==> A[i] == _A[i - 1]);
    assert (forall i: int :: count < i ==> A[i] == _A[i]);
    goto anon6_LoopDone, anon6_LoopBody;

  anon6_LoopBody:
    assume {:partition} idx < j;
    // <<< injected gate
    assert tid != nil && lock == tid;
    // injected gate >>>
    call a := READ_A_1(tid, j - 1);
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    // <<< injected gate
    assert tid != nil && lock == tid;
    // injected gate >>>
    call WRITE_A_1(tid, j, a);
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    j := j - 1;
    goto anon6_LoopHead;

  anon6_LoopDone:
    assume {:partition} j <= idx;
    goto anon4;

  anon4:
    // <<< injected gate
    assert tid != nil && lock == tid;
    // injected gate >>>
    call WRITE_A_1(tid, idx, v);
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    // <<< injected gate
    assert tid != nil && lock == tid;
    // injected gate >>>
    call WRITE_COUNT_1(tid, c + 1);
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assert sorted(A, count);
    // <<< injected gate
    assert tid != nil && lock == tid;
    // injected gate >>>
    call RELEASE_1(tid);
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon417, CallToYieldProc;

  anon02:
    assert og_pc
       || 
      (
        A == og_global_old_A
         && count == og_global_old_count
         && lock == og_global_old_lock
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (exists #tmp_0_second_A_new: [int]int, #tmp_1_second_idx: int :: 
        A == #tmp_0_second_A_new[#tmp_1_second_idx := v]
           && count == og_global_old_count + 1
           && lock == og_global_old_lock
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (forall second_i: int :: 
            og_global_old_count < second_i
               ==> #tmp_0_second_A_new[second_i] == og_global_old_A[second_i])
           && (forall second_i: int :: 
            #tmp_1_second_idx < second_i && second_i < og_global_old_count
               ==> #tmp_0_second_A_new[second_i + 1] == og_global_old_A[second_i])
           && (forall second_i: int :: 
            second_i < #tmp_1_second_idx
               ==> #tmp_0_second_A_new[second_i] == og_global_old_A[second_i])
           && (forall second_i: int :: 
            #tmp_1_second_idx <= second_i && second_i < og_global_old_count
               ==> og_global_old_A[second_i] >= v)
           && (forall second_i: int :: 
            0 <= second_i && second_i < #tmp_1_second_idx ==> og_global_old_A[second_i] < v)
           && 0 <= #tmp_1_second_idx
           && #tmp_1_second_idx <= og_global_old_count);
    assert og_pc
       ==> A == og_global_old_A
         && count == og_global_old_count
         && lock == og_global_old_lock
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := A == og_global_old_A
         && count == og_global_old_count
         && lock == og_global_old_lock
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (exists #tmp_0_second_A_new: [int]int, #tmp_1_second_idx: int :: 
        A == #tmp_0_second_A_new[#tmp_1_second_idx := v]
           && count == og_global_old_count + 1
           && lock == og_global_old_lock
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (forall second_i: int :: 
            og_global_old_count < second_i
               ==> #tmp_0_second_A_new[second_i] == og_global_old_A[second_i])
           && (forall second_i: int :: 
            #tmp_1_second_idx < second_i && second_i < og_global_old_count
               ==> #tmp_0_second_A_new[second_i + 1] == og_global_old_A[second_i])
           && (forall second_i: int :: 
            second_i < #tmp_1_second_idx
               ==> #tmp_0_second_A_new[second_i] == og_global_old_A[second_i])
           && (forall second_i: int :: 
            #tmp_1_second_idx <= second_i && second_i < og_global_old_count
               ==> og_global_old_A[second_i] >= v)
           && (forall second_i: int :: 
            0 <= second_i && second_i < #tmp_1_second_idx ==> og_global_old_A[second_i] < v)
           && 0 <= #tmp_1_second_idx
           && #tmp_1_second_idx <= og_global_old_count);
    havoc A, count, lock, pendingAsyncMultiset;
    assume og_pc || (count >= 0 && sorted(A, count));
    linear_tid_available, og_global_old_A, og_global_old_count, og_global_old_lock, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), A, count, lock, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume tid != nil;
    call _A := snapshot();
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    // <<< injected gate
    assert tid != nil;
    // injected gate >>>
    call ACQUIRE_1(tid);
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    idx := 0;
    // <<< injected gate
    assert tid != nil && lock == tid;
    // injected gate >>>
    call c := READ_COUNT_1(tid);
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    // <<< injected gate
    assert tid != nil && lock == tid;
    // injected gate >>>
    call a := READ_A_1(tid, idx);
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon5_LoopHead;

  anon425:
    assert og_pc
       || 
      (
        A == og_global_old_A
         && count == og_global_old_count
         && lock == og_global_old_lock
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (exists #tmp_0_second_A_new: [int]int, #tmp_1_second_idx: int :: 
        A == #tmp_0_second_A_new[#tmp_1_second_idx := v]
           && count == og_global_old_count + 1
           && lock == og_global_old_lock
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (forall second_i: int :: 
            og_global_old_count < second_i
               ==> #tmp_0_second_A_new[second_i] == og_global_old_A[second_i])
           && (forall second_i: int :: 
            #tmp_1_second_idx < second_i && second_i < og_global_old_count
               ==> #tmp_0_second_A_new[second_i + 1] == og_global_old_A[second_i])
           && (forall second_i: int :: 
            second_i < #tmp_1_second_idx
               ==> #tmp_0_second_A_new[second_i] == og_global_old_A[second_i])
           && (forall second_i: int :: 
            #tmp_1_second_idx <= second_i && second_i < og_global_old_count
               ==> og_global_old_A[second_i] >= v)
           && (forall second_i: int :: 
            0 <= second_i && second_i < #tmp_1_second_idx ==> og_global_old_A[second_i] < v)
           && 0 <= #tmp_1_second_idx
           && #tmp_1_second_idx <= og_global_old_count);
    assert og_pc
       ==> A == og_global_old_A
         && count == og_global_old_count
         && lock == og_global_old_lock
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := A == og_global_old_A
         && count == og_global_old_count
         && lock == og_global_old_lock
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (exists #tmp_0_second_A_new: [int]int, #tmp_1_second_idx: int :: 
        A == #tmp_0_second_A_new[#tmp_1_second_idx := v]
           && count == og_global_old_count + 1
           && lock == og_global_old_lock
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (forall second_i: int :: 
            og_global_old_count < second_i
               ==> #tmp_0_second_A_new[second_i] == og_global_old_A[second_i])
           && (forall second_i: int :: 
            #tmp_1_second_idx < second_i && second_i < og_global_old_count
               ==> #tmp_0_second_A_new[second_i + 1] == og_global_old_A[second_i])
           && (forall second_i: int :: 
            second_i < #tmp_1_second_idx
               ==> #tmp_0_second_A_new[second_i] == og_global_old_A[second_i])
           && (forall second_i: int :: 
            #tmp_1_second_idx <= second_i && second_i < og_global_old_count
               ==> og_global_old_A[second_i] >= v)
           && (forall second_i: int :: 
            0 <= second_i && second_i < #tmp_1_second_idx ==> og_global_old_A[second_i] < v)
           && 0 <= #tmp_1_second_idx
           && #tmp_1_second_idx <= og_global_old_count);
    assert og_ok;
    return;

  anon417:
    assert og_pc
       || 
      (
        A == og_global_old_A
         && count == og_global_old_count
         && lock == og_global_old_lock
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (exists #tmp_0_second_A_new: [int]int, #tmp_1_second_idx: int :: 
        A == #tmp_0_second_A_new[#tmp_1_second_idx := v]
           && count == og_global_old_count + 1
           && lock == og_global_old_lock
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (forall second_i: int :: 
            og_global_old_count < second_i
               ==> #tmp_0_second_A_new[second_i] == og_global_old_A[second_i])
           && (forall second_i: int :: 
            #tmp_1_second_idx < second_i && second_i < og_global_old_count
               ==> #tmp_0_second_A_new[second_i + 1] == og_global_old_A[second_i])
           && (forall second_i: int :: 
            second_i < #tmp_1_second_idx
               ==> #tmp_0_second_A_new[second_i] == og_global_old_A[second_i])
           && (forall second_i: int :: 
            #tmp_1_second_idx <= second_i && second_i < og_global_old_count
               ==> og_global_old_A[second_i] >= v)
           && (forall second_i: int :: 
            0 <= second_i && second_i < #tmp_1_second_idx ==> og_global_old_A[second_i] < v)
           && 0 <= #tmp_1_second_idx
           && #tmp_1_second_idx <= og_global_old_count);
    assert og_pc
       ==> A == og_global_old_A
         && count == og_global_old_count
         && lock == og_global_old_lock
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := A == og_global_old_A
         && count == og_global_old_count
         && lock == og_global_old_lock
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (exists #tmp_0_second_A_new: [int]int, #tmp_1_second_idx: int :: 
        A == #tmp_0_second_A_new[#tmp_1_second_idx := v]
           && count == og_global_old_count + 1
           && lock == og_global_old_lock
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (forall second_i: int :: 
            og_global_old_count < second_i
               ==> #tmp_0_second_A_new[second_i] == og_global_old_A[second_i])
           && (forall second_i: int :: 
            #tmp_1_second_idx < second_i && second_i < og_global_old_count
               ==> #tmp_0_second_A_new[second_i + 1] == og_global_old_A[second_i])
           && (forall second_i: int :: 
            second_i < #tmp_1_second_idx
               ==> #tmp_0_second_A_new[second_i] == og_global_old_A[second_i])
           && (forall second_i: int :: 
            #tmp_1_second_idx <= second_i && second_i < og_global_old_count
               ==> og_global_old_A[second_i] >= v)
           && (forall second_i: int :: 
            0 <= second_i && second_i < #tmp_1_second_idx ==> og_global_old_A[second_i] < v)
           && 0 <= #tmp_1_second_idx
           && #tmp_1_second_idx <= og_global_old_count);
    havoc A, count, lock, pendingAsyncMultiset;
    assume og_pc || (count >= 0 && sorted(A, count));
    linear_tid_available, og_global_old_A, og_global_old_count, og_global_old_lock, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), A, count, lock, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon425, CallToYieldProc;

  CallToYieldProc:
    call og_yield_1(linear_tid_available, og_global_old_A, og_global_old_count, og_global_old_lock, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



procedure {:inline 1} Impl_YieldChecker_insert_1(linear_tid_in: [Tid]bool, 
    og_global_old_A: [int]int, 
    og_global_old_count: int, 
    og_global_old_lock: Tid, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



implementation {:inline 1} Impl_YieldChecker_insert_1(linear_tid_in: [Tid]bool, 
    og_global_old_A: [int]int, 
    og_global_old_count: int, 
    og_global_old_lock: Tid, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var idx: int;
  var j: int;
  var a: int;
  var c: int;
  var _A: [int]int;
  var tid: Tid;
  var v: int;
  var og_local_old_A: [int]int;
  var og_local_old_count: int;
  var og_local_old_lock: Tid;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0, L1;

  exit:
    return;

  L0:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume tid != nil;
    assert tid != nil;
    assume false;
    return;

  L1:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume false;
    return;
}



procedure {:inline 1} og_yield_1(linear_tid_in: [Tid]bool, 
    og_global_old_A: [int]int, 
    og_global_old_count: int, 
    og_global_old_lock: Tid, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



implementation {:inline 1} og_yield_1(linear_tid_in: [Tid]bool, 
    og_global_old_A: [int]int, 
    og_global_old_count: int, 
    og_global_old_lock: Tid, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{

  enter:
    goto L_0;

  L_0:
    call Impl_YieldChecker_insert_1(linear_tid_in, og_global_old_A, og_global_old_count, og_global_old_lock, og_global_old_pendingAsyncMultiset);
    return;
}


