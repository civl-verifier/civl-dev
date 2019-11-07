// -*- boogie-prover-local-args: ("/useArrayTheory") -*-

/*
 * Copyright (c) 2019, Oracle and/or its affiliates. All rights reserved.
 */

// =============================================================================
// Linear thread identifiers
// =============================================================================
type Tid;
function {:builtin "MapConst"} MapConstTidBool(bool) : [Tid]bool;
function {:inline}{:linear "tid"} TidCollector(tid:Tid) : [Tid]bool
{
  MapConstTidBool(false)[tid := true]
}
function {:inline} {:linear "tid"} TidSetCollector(x: [Tid]bool) : [Tid]bool
{
  x
}
type TidSet = [Tid]bool;
function EmptyTidSet() : TidSet
{ (lambda t : Tid :: false) }


// =============================================================================
// A lock is a record consisting of a flag indicating whether the lock
// is held in exclusive or shared mode and a set of thread identifiers
// who hold the lock. The associated atomic steps AcquireLock{Shared,Exclusive}
// and ReleaseLock{Shared,Exclusive} maintain the invariant that a lock
// held in exclusive mode has exactly one holder, i.e. tids contains
// exactly one element.
// =============================================================================
type {:datatype} Lock;
function {:constructor} Lock(exclusive : bool, tids: TidSet) : Lock;

var {:layer 0, 5} lock : Lock;

procedure {:yields} {:layer 0} {:refines "A_AcquireLockShared"} AcquireLockShared({:linear "tid"} tid: Tid);
procedure {:right} {:layer 1, 5} A_AcquireLockShared({:linear "tid"} tid: Tid)
modifies lock;
{
  assume !exclusive#Lock(lock) && !tids#Lock(lock)[tid];
  lock := Lock(false, tids#Lock(lock)[tid:=true]);
}

procedure {:yields} {:layer 0} {:refines "A_AcquireLockExclusive"} AcquireLockExclusive({:linear "tid"} tid: Tid);
procedure {:right} {:layer 1, 5} A_AcquireLockExclusive({:linear "tid"} tid: Tid)
modifies lock;
{
  assume !exclusive#Lock(lock) && tids#Lock(lock) == EmptyTidSet();
  lock := Lock(true, tids#Lock(lock)[tid:=true]);
}

function HoldsLock(tid: Tid, lock: Lock) : bool
{
  tids#Lock(lock)[tid]
}

procedure {:yields} {:layer 0} {:refines "A_ReleaseLockShared"} ReleaseLockShared({:linear "tid"} tid: Tid);
procedure {:left} {:layer 1, 5} A_ReleaseLockShared({:linear "tid"} tid: Tid)
modifies lock;
{
  assert !exclusive#Lock(lock) && HoldsLock(tid, lock);
  lock := Lock(false, tids#Lock(lock)[tid:=true]);
}

function HoldsLockExclusive(tid: Tid, lock: Lock) : bool
{
  exclusive#Lock(lock) && tids#Lock(lock) == EmptyTidSet()[tid:=true]
}

procedure {:yields} {:layer 0} {:refines "A_ReleaseLockExclusive"} ReleaseLockExclusive({:linear "tid"} tid: Tid);
procedure {:left} {:layer 1, 5} A_ReleaseLockExclusive({:linear "tid"} tid: Tid)
modifies lock;
{
  assert HoldsLockExclusive(tid, lock);
  lock := Lock(false, EmptyTidSet());
}

// =============================================================================
// The algorithm
// =============================================================================

type SetInt = [int]bool;

var {:layer 0, 6} latest : SetInt;
var {:layer 0, 6} copy : SetInt;
var {:layer 0, 6} copy_bound : int;
var {:layer 0, 6} requested_copy_bound : int; 

var {:layer 0, 6} copy_thread : Tid;

var {:layer 0, 6} is_running : [Tid]bool; 
var {:layer 0, 6} N : int;

var {:layer 0, 6} {:linear "tid"} unallocated:[Tid]bool;

// =============================================================================
// Main
// =============================================================================

// Allocate a previously unallocated Tid.
procedure {:yields} {:layer 0} {:refines "A_Allocate"} Allocate()
  returns ({:linear "tid"} tid: Tid);
procedure {:right} {:layer 1, 6} A_Allocate() returns ({:linear "tid"} tid: Tid)
modifies unallocated;
{
  assume unallocated[tid];
  unallocated[tid] := false;
}

// All unallocated are running
function UnallocatedRunning(unallocated, is_running: [Tid]bool): bool
{ (forall utid : Tid :: unallocated[utid] ==> is_running[utid]) }

// Models the large atomic step in the body of main. In the actual implementation,
// this atomic step asynchronously calls Write and potentially Copy. I don't know
// how to express this in CIVL because atomic procedures can't call other
// procedures. As a result, this doesn't actually check that the preconditions
// for Write and Copy hold at the call sites.
procedure {:yields} {:layer 0} {:refines "A_MainLoopBodyLow"} MainLoopBodyLow({:linear "tid"} copy_tid: Tid)
  returns (spawn_copy: bool, to_write: int);
procedure {:atomic} {:layer 1, 5} A_MainLoopBodyLow({:linear "tid"} copy_tid: Tid)
  returns (spawn_copy: bool, to_write: int)
modifies requested_copy_bound, is_running, copy_thread, N, unallocated;
{
  assert requested_copy_bound <= N;
  spawn_copy := false;

  if (*) {
    requested_copy_bound := N;
    if (!is_running[copy_thread]) {
       copy_thread := copy_tid;
       spawn_copy := true;
    }
  }
  N := N + 1;
  to_write := N;
}

// We need to show that the atomic action closely matching the implementation A_MainLoopBodyLow
// refines the more abstract atomic action A_MainLoopBody, which is in terms of the inductive
// invariant. I don't think there's a way to state directly that an atomic action refines
// another atomic action, so I added this yielding procedure MainLoopBody which just calls
// MainLoopBodyLow and refines A_MainLoopBody.
procedure {:yields} {:layer 5} {:refines "A_MainLoopBody"} MainLoopBody({:linear "tid"} tid: Tid, {:linear "tid"} copy_tid: Tid)
  returns (spawn_copy: bool, to_write: int)
requires {:layer 5} tid == main_tid;
requires {:layer 5} requested_copy_bound <= N;
requires {:layer 5} is_running[copy_tid];
requires {:layer 5} UnallocatedRunning(unallocated, is_running);
requires {:layer 5} N > 0;
ensures {:layer 5} requested_copy_bound <= N;
ensures {:layer 5} spawn_copy ==> copy_tid == copy_thread;
ensures {:layer 5} UnallocatedRunning(unallocated, is_running);
ensures {:layer 5} to_write <= N;
ensures {:layer 5} is_running[copy_tid];
ensures {:layer 5} N > 0;
ensures {:layer 5} spawn_copy ==> requested_copy_bound > 0;
{
  yield;
  assert {:layer 5} requested_copy_bound <= N;
  assert {:layer 5} is_running[copy_tid];
  assert {:layer 5} UnallocatedRunning(unallocated, is_running);
  assert {:layer 5} N > 0;

  call spawn_copy, to_write := MainLoopBodyLow(copy_tid);

  yield;
  assert {:layer 5} requested_copy_bound <= N;
  assert {:layer 5} spawn_copy ==> copy_tid == copy_thread;
  assert {:layer 5} to_write <= N;
  assert {:layer 5} UnallocatedRunning(unallocated, is_running);
  assert {:layer 5} is_running[copy_tid];
  assert {:layer 5} N > 0;
  assert {:layer 5} spawn_copy ==> requested_copy_bound > 0;
}

procedure {:atomic} {:layer 6} A_MainLoopBody({:linear "tid"} tid: Tid, {:linear "tid"} copy_tid: Tid)
  returns (spawn_copy: bool, to_write: int)
modifies copy, latest, N, copy_bound, requested_copy_bound, is_running, copy_thread, unallocated;
{
  assert Inv(copy, latest, N, copy_bound, requested_copy_bound, is_running, copy_thread);
  havoc copy, latest, N, copy_bound, requested_copy_bound, is_running, copy_thread;
  assume Inv(copy, latest, N, copy_bound, requested_copy_bound, is_running, copy_thread);
  assume !spawn_copy ==> old(is_running[copy_thread]) || !is_running[copy_thread];
}

function MainPostCond(copy_bound, requested_copy_bound: int, copy, latest: SetInt) : bool
{
  requested_copy_bound != 0 ==>
  (   copy_bound == requested_copy_bound
   && copy == (lambda n : int :: latest[n] && n <= requested_copy_bound))
}

// Constant used to enforce that only one thread runs Main.
const main_tid : Tid;

// Entry point of the algorithm.
procedure {:yields} {:layer 6} Main({:linear "tid"} tid: Tid)
requires {:layer 5} tid == main_tid;
requires {:layer 5} UnallocatedRunning(unallocated, is_running);
requires {:layer 5} N > 0; 
requires {:layer 5, 6} N == copy_bound;
requires {:layer 5, 6} requested_copy_bound == copy_bound;
requires {:layer 6} copy == (lambda n : int :: latest[n] && n <= copy_bound);
requires {:layer 6} (forall n : int :: latest[n] ==> n <= N);
requires {:layer 6} !is_running[copy_thread];
ensures {:layer 6} MainPostCond(copy_bound, requested_copy_bound, copy, latest);
{
  var spawn_copy : bool;
  var {:linear "tid"} write_tid : Tid;
  var {:linear "tid"} copy_tid : Tid;
  var to_write : int;

  yield;
  assert {:layer 5} tid == main_tid; 
  assert {:layer 5} N > 0; 
  assert {:layer 5, 6} requested_copy_bound <= N;
  assert {:layer 6} copy == (lambda n : int :: latest[n] && n <= copy_bound);
  assert {:layer 6} (forall n : int :: latest[n] ==> n <= N);
  assert {:layer 6} !is_running[copy_thread];
  assert {:layer 6} copy_bound == requested_copy_bound;
  assert {:layer 5} UnallocatedRunning(unallocated, is_running);

  while (*)
  invariant {:layer 5} requested_copy_bound <= N;
  invariant {:layer 5} N > 0;
  invariant {:layer 5} UnallocatedRunning(unallocated, is_running);
  invariant {:layer 6} Inv(copy, latest, N, copy_bound, requested_copy_bound, is_running, copy_thread);
  invariant {:layer 6} !is_running[copy_thread];
  {
    // Allocate a Tid for the upcoming write call. It doesn't matter where this happens
    // and A_Allocate is a right mover, so I put it before the call to MainBody to avoid
    // having to add another yield.
    call write_tid := Allocate();
    // Allocate a thread that may be used for Copy.
    call copy_tid := Allocate();

    call spawn_copy, to_write := MainLoopBody(tid, copy_tid);

    async call Write(write_tid, to_write);
    if (spawn_copy) {
      async call Copy(copy_tid);
    } 
    yield;
    assert {:layer 5} requested_copy_bound <= N;
    assert {:layer 5} UnallocatedRunning(unallocated, is_running);
    assert {:layer 5} N > 0; 
    assert {:layer 6} !is_running[copy_thread];
    assert {:layer 6} Inv(copy, latest, N, copy_bound, requested_copy_bound, is_running, copy_thread);
  }
  yield;
  assert {:layer 6} MainPostCond(copy_bound, requested_copy_bound, copy, latest);
}

// =============================================================================
// Write
// =============================================================================

// First atomic step in Write
//
// The actual implementation only waits for !is_running[copy_thread], but it is sound
// to generalize this by weakening the enabling condition (assume). This abstraction
// makes this action a right mover.
procedure {:yields} {:layer 0} {:refines "A_WaitNotRunning"} WaitNotRunning(n: int);
procedure {:right} {:layer 1, 5} A_WaitNotRunning(n: int)
{
  assert n <= N;
  assume !is_running[copy_thread] || n <= requested_copy_bound;
}

// Returns copy_bound
procedure {:yields} {:layer 0} {:refines "A_Get_Copy_Bound"} Get_Copy_Bound({:linear "tid"} tid: Tid) returns (c : int);
procedure {:both} {:layer 1, 5} A_Get_Copy_Bound({:linear "tid"} tid: Tid) returns (c : int)
{
  assert HoldsLock(tid, lock);
  c := copy_bound;
}

// Add an element to the set copy
// Requires a shared lock so that this is a both mover
procedure {:yields} {:layer 0} {:refines "A_AddToCopy"} AddToCopy({:linear "tid"} tid: Tid, n: int);
procedure {:both} {:layer 1, 5} A_AddToCopy({:linear "tid"} tid: Tid, n: int)
modifies copy;
{
  assert HoldsLock(tid, lock);
  copy := copy[n:=true];
}

// Add an element to the set latest
// Requires a shared lock so that this is a both mover
procedure {:yields} {:layer 0} {:refines "A_AddToLatest"} AddToLatest({:linear "tid"} tid: Tid, n: int);
procedure {:both} {:layer 1, 5} A_AddToLatest({:linear "tid"} tid: Tid, n: int)
modifies latest;
{
  assert HoldsLock(tid, lock);
  latest := latest[n:=true];
}

// Full Write procedure.
//
// Write is asynchronously called with an argument (N+1), but the same atomic step
// also increments N after calling Write, so the precondition n <= N does hold.
procedure {:yields} {:layer 5} {:refines "A_Write"} Write({:linear "tid"} tid: Tid,  n: int)
requires {:layer 5} n <= N;
//requires {:layer 5} !is_running[copy_thread] || n <= requested_copy_bound; 
{
  var local_copy_bound : int;

  yield;
  assert {:layer 5} n <= N;
  //assert {:layer 5} !is_running[copy_thread] || n <= requested_copy_bound; 

  call WaitNotRunning(n);

  call AcquireLockShared(tid);
  call local_copy_bound := Get_Copy_Bound(tid);
  if (n <= local_copy_bound) {
    call AddToCopy(tid, n);
  }
  call AddToLatest(tid, n);
  call ReleaseLockShared(tid);
  yield;
}

// Atomic summary of Write, basically just gets rid of the wait for
// !is_running[copy_thread];
//
// A more precise abstraction is
//
//   assume !is_running[copy_thread] || n <= requested_copy_bound;
//   if (n <= copy_bound) {
//     copy[n] := true;
//   }
//   latest[n] := true;
//
// but we do the following so that we can make A_Copy and A_Write left movers.
procedure {:left} {:layer 6} A_Write({:linear "tid"} tid: Tid, n: int)
modifies copy, latest, N, copy_bound, requested_copy_bound, is_running, copy_thread;
{
  assert Inv(copy, latest, N, copy_bound, requested_copy_bound, is_running, copy_thread);
  havoc copy, latest, N, copy_bound, requested_copy_bound, is_running, copy_thread;
  assume Inv(copy, latest, N, copy_bound, requested_copy_bound, is_running, copy_thread);
  assume is_running[copy_thread] == old(is_running[copy_thread]);
}

// =============================================================================
// Copy
// =============================================================================

// Models evaluating the loop condition in Copy to true.
procedure {:yields} {:layer 0} {:refines "A_Copy_Continue"}
  Copy_Continue(creating_copy_bound: int) returns (next_copy_bound: int);
procedure {:right} {:layer 1, 5} A_Copy_Continue(creating_copy_bound: int)
  returns (next_copy_bound: int)
{
  assert creating_copy_bound <= requested_copy_bound;
  assume creating_copy_bound != requested_copy_bound;
  assume next_copy_bound <= requested_copy_bound;
}

// Models evaluating the loop condition in Copy to false. In the implementation,
// evaluating the loop condition to false happens in the same atomic step that
// sets is_running to false. This is actually necessary for correctness.
procedure {:yields} {:layer 0} {:refines "A_Copy_Stop"}
  Copy_Stop(tid: Tid, creating_copy_bound: int);
procedure {:atomic} {:layer 1, 5} A_Copy_Stop(tid: Tid, creating_copy_bound: int)
modifies is_running;
{
  assume creating_copy_bound == requested_copy_bound;
  is_running[tid] :=false;
}

// Initialize copy by setting it to latest
// Requires exclusive lock to be a both mover
procedure {:yields} {:layer 0} {:refines "A_CreateCopy"} CreateCopy({:linear "tid"} tid: Tid);
procedure {:both} {:layer 1, 4} A_CreateCopy({:linear "tid"} tid: Tid)
modifies copy;
{
  assert HoldsLockExclusive(tid, lock);
  copy := latest;
}

// Set copy_bound to n
// Requires exclusive lock to be a both mover
procedure {:yields} {:layer 0} {:refines "A_Set_Copy_Bound"} Set_Copy_Bound({:linear "tid"} tid: Tid, n: int);
procedure {:both} {:layer 1, 4} A_Set_Copy_Bound({:linear "tid"} tid: Tid, n: int)
modifies copy_bound;
{
  assert HoldsLockExclusive(tid, lock);
  copy_bound := n;
}

// Yielding procedure that does the actual copy and copy_bound work in Copy.
procedure {:yields} {:layer 4} {:refines "A_DoCopy"}
  DoCopy({:linear "tid"} tid: Tid, creating_copy_bound: int)
requires {:layer 4} HoldsLockExclusive(tid, lock);
ensures {:layer 4} HoldsLockExclusive(tid, lock);
{
  yield;
  call CreateCopy(tid);
  call Set_Copy_Bound(tid, creating_copy_bound);
  yield;
  assert {:layer 4} HoldsLockExclusive(tid, lock);
}

// Generalization of the part of the body of Copy that sets copy and copy_bound.
// The atomicity of updating both variables is possible because the corresponding
// lower layer actions are done under an exclusive lock. Without the generalization
// this would just be:
//
//   copy := latest;
//   copy_bound := creating_copy_bound;
//
// The generalization makes this action a right mover, which is necessary for
// summarizing the loop in Copy. Essentially, this action says that all iterations
// of the loop in Copy just havoc copy, except for the last one. In other words,
// only the last iteration of the loop in Copy matters.
//
// Note that the intermediate iterations of Copy do matter for crash safety of
// the algorithm, so that will have to be addressed at a lower layer. Decoupling
// crash safety from other correctness properties seems to be a benefit of the
// CIVL approach.
procedure {:right} {:layer 5}
  A_DoCopy({:linear "tid"} tid: Tid, creating_copy_bound: int)
modifies copy_bound, copy;
{
  assert is_running[copy_thread];
  assert tid == copy_thread;
  assert creating_copy_bound <= requested_copy_bound;
  assert HoldsLockExclusive(tid, lock);

  if (creating_copy_bound == requested_copy_bound) {
    copy := latest;
  } else {
    havoc copy;
  }
  copy_bound := creating_copy_bound;
}

// The loop condition from the implementation is expressed via the non-deterministic
// if-then-else. Moving the loop condition into the body is necessary just to express
// that is_running[tid] is set to false in the same atomic step that evaluates the
// loop condition to false. Splitting the evaluation of the loop condition into two
// atomic actions allows for the simple summary of Copy.
//
// Eventually, this procedure will need to model locks, which will require adding a
// lock release on exit. This lock release either needs to be in Copy_Stop or before
// the return. Putting it in Copy_Stop seems a bit strange, but putting it outside
// of Copy_Stop means that the lock is held even after setting is_running[tid] to false,
// which also seems a bit strange.
procedure {:yields} {:layer 5} {:refines "A_Copy"} Copy({:linear "tid"} tid: Tid)
requires {:layer 5} 0 <= requested_copy_bound;
requires {:layer 5} tid == copy_thread;
requires {:layer 5} is_running[tid];
{
  var creating_copy_bound: int;
  creating_copy_bound := 0;

  yield;
  assert {:layer 5} creating_copy_bound <= requested_copy_bound;
  assert {:layer 5} 0 <= requested_copy_bound; 
  assert {:layer 5} is_running[tid];
  assert {:layer 5} tid == copy_thread;

  call AcquireLockExclusive(tid);

  while (true)
  invariant {:layer 5} {:terminates} true;
  invariant {:layer 5} creating_copy_bound <= requested_copy_bound;
  invariant {:layer 5} 0 <= requested_copy_bound; 
  invariant {:layer 5} (requested_copy_bound != 0 && creating_copy_bound == requested_copy_bound) ==>
    (copy == latest && copy_bound == requested_copy_bound);
  invariant {:layer 4} HoldsLockExclusive(tid, lock); 
  {
    if (*) {
      call creating_copy_bound := Copy_Continue(creating_copy_bound);
    } else {
      call Copy_Stop(tid, creating_copy_bound);
      call ReleaseLockExclusive(tid);
      assert {:layer 5} requested_copy_bound != 0 ==> copy == latest && copy_bound == requested_copy_bound; 
      yield;
      return;
    }
    call DoCopy(tid, creating_copy_bound);
  }
  assert {:layer 5} false;
  yield;
} 

// Since every atomic action in the loop is a right mover, except for the last one
// (evaluating the loop condition to false), the loop can be summarized by running
// every iteration with no interleaving. Only the last iteration matters (it overwrites
// all previous ones), so the summary is just the last iteration.
//
// The above reasoning relies on the fact that there's at least one iteration of the
// loop.
//
// A more precise abstraction is
//
//   copy := latest;
//   copy_bound := requested_copy_bound;
//   is_running[copy_thread] := false;
//
// but we do the following so that we can make A_Copy and A_Write left movers.
//
// This currently fails the check for non-blocking because of an inability to
// instantiate the existential quantifiers in that check. The following should
// work (checked manually on the desugared boogie file):
//
//   is_running -> old(is_running)[old(copy_thread):=false]
//   copy -> if (!old(is_running[copy_thread])) then old(copy) else old(latest)
//   copy_bound -> requested_copy_bound
procedure {:left} {:layer 6} A_Copy({:linear "tid"} tid: Tid)
modifies copy, latest, N, copy_bound, requested_copy_bound, is_running, copy_thread;
{
  assert Inv(copy, latest, N, copy_bound, requested_copy_bound, is_running, copy_thread);
  havoc copy, latest, N, copy_bound, requested_copy_bound, is_running, copy_thread;
  assume !is_running[copy_thread];
  assume Inv(copy, latest, N, copy_bound, requested_copy_bound, is_running, copy_thread);
}

function Inv(copy, latest: SetInt, N, copy_bound, requested_copy_bound: int, is_running: [Tid]bool, copy_thread: Tid) : bool
{
     (forall n : int :: latest[n] ==> n <= N)
  && requested_copy_bound <= N
  && (is_running[copy_thread] ==>
        (forall n : int :: latest[n] ==> n <= requested_copy_bound))
  && (!is_running[copy_thread] ==> MainPostCond(copy_bound, requested_copy_bound, copy, latest))
}
