// Boogie program verifier version 2.4.1.10503, Copyright (c) 2003-2014, Microsoft.
// Command Line Options: /noWitnessInference /noCommutativityTriggers /noVerify /CivlDesugaredFile:desugared_files/wsq.desugared.bpl ../wsq.bpl

type Tid;

const nil: Tid;

function {:builtin "MapConst"} MapConstBool(bool) : [Tid]bool;

function {:inline} TidCollector(x: Tid) : [Tid]bool
{
  MapConstBool(false)[x := true]
}

var H: int;

var T: int;

var items: [int]int;

var status: [int]bool;

var take_in_cs: bool;

var put_in_cs: bool;

var steal_in_cs: [Tid]bool;

var h_ss: [Tid]int;

var t_ss: [Tid]int;

const IN_Q: bool;

const NOT_IN_Q: bool;

axiom IN_Q <==> true;

axiom NOT_IN_Q <==> false;

const unique EMPTY: int;

const unique NIL: Tid;

const unique ptTid: Tid;

axiom ptTid != NIL;

function {:inline} stealerTid(tid: Tid) : bool
{
  tid != NIL && tid != ptTid
}

function {:inline} ideasInv(put_in_cs: bool, 
    items: [int]int, 
    status: [int]bool, 
    H: int, 
    T: int, 
    take_in_cs: bool, 
    steal_in_cs: [Tid]bool, 
    h_ss: [Tid]int, 
    t_ss: [Tid]int)
   : bool
{
  (take_in_cs && h_ss[ptTid] < t_ss[ptTid]
       ==> t_ss[ptTid] == T && H <= T && items[T] != EMPTY && (status[T] <==> IN_Q))
     && (put_in_cs ==> !take_in_cs)
     && (take_in_cs ==> !put_in_cs)
     && (take_in_cs && H != h_ss[ptTid] ==> H > h_ss[ptTid])
     && (forall td: Tid :: 
      stealerTid(td) && steal_in_cs[td] && H == h_ss[td] && H < t_ss[td]
         ==> items[H] != EMPTY && (status[H] <==> IN_Q))
     && (forall td: Tid :: 
      stealerTid(td) && steal_in_cs[td] && H != h_ss[td] ==> H > h_ss[td])
}

function {:inline} queueInv(steal_in_cs: [Tid]bool, 
    put_in_cs: bool, 
    take_in_cs: bool, 
    items: [int]int, 
    status: [int]bool, 
    _H: int, 
    _T: int)
   : bool
{
  (forall i: int :: 
    _H <= i && i <= _T ==> (status[i] <==> IN_Q) && items[i] != EMPTY)
}

function {:inline} emptyInv(put_in_cs: bool, take_in_cs: bool, items: [int]int, status: [int]bool, T: int)
   : bool
{
  (forall i: int :: 
    i >= T && !put_in_cs && !take_in_cs
       ==> (status[i] <==> NOT_IN_Q) && items[i] == EMPTY)
}

function {:inline} putInv(items: [int]int, status: [int]bool, H: int, T: int) : bool
{
  (forall i: int :: 
    H <= i && i < T ==> (status[i] <==> IN_Q) && items[i] != EMPTY)
}

function {:inline} takeInv(items: [int]int, status: [int]bool, H: int, T: int, t: int, h: int) : bool
{
  (forall i: int :: 
    h <= i && i <= t ==> (status[i] <==> IN_Q) && items[i] != EMPTY && t == T)
}

procedure {:inline 1} GhostRead() returns (oldH: int, oldT: int);



implementation {:inline 1} GhostRead() returns (oldH: int, oldT: int)
{
  /*** structured program:
    oldH := H;
    oldT := T;
  **** end structured program */

  anon0:
    oldH := H;
    oldT := T;
    return;
}



procedure {:inline 1} GhostReadStatus() returns (oldStatus: bool);



implementation {:inline 1} GhostReadStatus() returns (oldStatus: bool)
{
  /*** structured program:
    oldStatus := status[T];
  **** end structured program */

  anon0:
    oldStatus := status[T];
    return;
}



type {:datatype} PendingAsync;

var pendingAsyncMultiset: [PendingAsync]int;

function {:constructor} PendingAsync_put(tid: Tid, task: int) : PendingAsync;

procedure {:inline 1} AddPendingAsync_put(tid: Tid, task: int);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_put(tid: Tid, task: int)
{

  L:
    pendingAsyncMultiset[PendingAsync_put(tid, task)] := pendingAsyncMultiset[PendingAsync_put(tid, task)] + 1;
    return;
}



function {:constructor} PendingAsync_take(tid: Tid) : PendingAsync;

procedure {:inline 1} AddPendingAsync_take(tid: Tid);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_take(tid: Tid)
{

  L:
    pendingAsyncMultiset[PendingAsync_take(tid)] := pendingAsyncMultiset[PendingAsync_take(tid)] + 1;
    return;
}



function {:constructor} PendingAsync_steal(tid: Tid) : PendingAsync;

procedure {:inline 1} AddPendingAsync_steal(tid: Tid);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_steal(tid: Tid)
{

  L:
    pendingAsyncMultiset[PendingAsync_steal(tid)] := pendingAsyncMultiset[PendingAsync_steal(tid)] + 1;
    return;
}



function {:constructor} PendingAsync_readH_take(tid: Tid) : PendingAsync;

procedure {:inline 1} AddPendingAsync_readH_take(tid: Tid);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_readH_take(tid: Tid)
{

  L:
    pendingAsyncMultiset[PendingAsync_readH_take(tid)] := pendingAsyncMultiset[PendingAsync_readH_take(tid)] + 1;
    return;
}



function {:constructor} PendingAsync_readH_steal(tid: Tid) : PendingAsync;

procedure {:inline 1} AddPendingAsync_readH_steal(tid: Tid);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_readH_steal(tid: Tid)
{

  L:
    pendingAsyncMultiset[PendingAsync_readH_steal(tid)] := pendingAsyncMultiset[PendingAsync_readH_steal(tid)] + 1;
    return;
}



function {:constructor} PendingAsync_readT_take_init(tid: Tid) : PendingAsync;

procedure {:inline 1} AddPendingAsync_readT_take_init(tid: Tid);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_readT_take_init(tid: Tid)
{

  L:
    pendingAsyncMultiset[PendingAsync_readT_take_init(tid)] := pendingAsyncMultiset[PendingAsync_readT_take_init(tid)] + 1;
    return;
}



function {:constructor} PendingAsync_readT_put(tid: Tid) : PendingAsync;

procedure {:inline 1} AddPendingAsync_readT_put(tid: Tid);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_readT_put(tid: Tid)
{

  L:
    pendingAsyncMultiset[PendingAsync_readT_put(tid)] := pendingAsyncMultiset[PendingAsync_readT_put(tid)] + 1;
    return;
}



function {:constructor} PendingAsync_readT_steal(tid: Tid) : PendingAsync;

procedure {:inline 1} AddPendingAsync_readT_steal(tid: Tid);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_readT_steal(tid: Tid)
{

  L:
    pendingAsyncMultiset[PendingAsync_readT_steal(tid)] := pendingAsyncMultiset[PendingAsync_readT_steal(tid)] + 1;
    return;
}



function {:constructor} PendingAsync_readItems(tid: Tid, ind: int) : PendingAsync;

procedure {:inline 1} AddPendingAsync_readItems(tid: Tid, ind: int);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_readItems(tid: Tid, ind: int)
{

  L:
    pendingAsyncMultiset[PendingAsync_readItems(tid, ind)] := pendingAsyncMultiset[PendingAsync_readItems(tid, ind)] + 1;
    return;
}



function {:constructor} PendingAsync_writeT_put(tid: Tid, val: int) : PendingAsync;

procedure {:inline 1} AddPendingAsync_writeT_put(tid: Tid, val: int);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_writeT_put(tid: Tid, val: int)
{

  L:
    pendingAsyncMultiset[PendingAsync_writeT_put(tid, val)] := pendingAsyncMultiset[PendingAsync_writeT_put(tid, val)] + 1;
    return;
}



function {:constructor} PendingAsync_writeT_take(tid: Tid, val: int) : PendingAsync;

procedure {:inline 1} AddPendingAsync_writeT_take(tid: Tid, val: int);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_writeT_take(tid: Tid, val: int)
{

  L:
    pendingAsyncMultiset[PendingAsync_writeT_take(tid, val)] := pendingAsyncMultiset[PendingAsync_writeT_take(tid, val)] + 1;
    return;
}



function {:constructor} PendingAsync_writeT_take_abort(tid: Tid, val: int) : PendingAsync;

procedure {:inline 1} AddPendingAsync_writeT_take_abort(tid: Tid, val: int);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_writeT_take_abort(tid: Tid, val: int)
{

  L:
    pendingAsyncMultiset[PendingAsync_writeT_take_abort(tid, val)] := pendingAsyncMultiset[PendingAsync_writeT_take_abort(tid, val)] + 1;
    return;
}



function {:constructor} PendingAsync_writeT_take_eq(tid: Tid, val: int) : PendingAsync;

procedure {:inline 1} AddPendingAsync_writeT_take_eq(tid: Tid, val: int);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_writeT_take_eq(tid: Tid, val: int)
{

  L:
    pendingAsyncMultiset[PendingAsync_writeT_take_eq(tid, val)] := pendingAsyncMultiset[PendingAsync_writeT_take_eq(tid, val)] + 1;
    return;
}



function {:constructor} PendingAsync_takeExitCS(tid: Tid) : PendingAsync;

procedure {:inline 1} AddPendingAsync_takeExitCS(tid: Tid);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_takeExitCS(tid: Tid)
{

  L:
    pendingAsyncMultiset[PendingAsync_takeExitCS(tid)] := pendingAsyncMultiset[PendingAsync_takeExitCS(tid)] + 1;
    return;
}



function {:constructor} PendingAsync_stealExitCS(tid: Tid) : PendingAsync;

procedure {:inline 1} AddPendingAsync_stealExitCS(tid: Tid);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_stealExitCS(tid: Tid)
{

  L:
    pendingAsyncMultiset[PendingAsync_stealExitCS(tid)] := pendingAsyncMultiset[PendingAsync_stealExitCS(tid)] + 1;
    return;
}



function {:constructor} PendingAsync_writeItems(tid: Tid, idx: int, val: int) : PendingAsync;

procedure {:inline 1} AddPendingAsync_writeItems(tid: Tid, idx: int, val: int);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_writeItems(tid: Tid, idx: int, val: int)
{

  L:
    pendingAsyncMultiset[PendingAsync_writeItems(tid, idx, val)] := pendingAsyncMultiset[PendingAsync_writeItems(tid, idx, val)] + 1;
    return;
}



function {:constructor} PendingAsync_writeItems_put(tid: Tid, idx: int, val: int) : PendingAsync;

procedure {:inline 1} AddPendingAsync_writeItems_put(tid: Tid, idx: int, val: int);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_writeItems_put(tid: Tid, idx: int, val: int)
{

  L:
    pendingAsyncMultiset[PendingAsync_writeItems_put(tid, idx, val)] := pendingAsyncMultiset[PendingAsync_writeItems_put(tid, idx, val)] + 1;
    return;
}



function {:constructor} PendingAsync_CAS_H_take(tid: Tid, prevVal: int, val: int) : PendingAsync;

procedure {:inline 1} AddPendingAsync_CAS_H_take(tid: Tid, prevVal: int, val: int);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_CAS_H_take(tid: Tid, prevVal: int, val: int)
{

  L:
    pendingAsyncMultiset[PendingAsync_CAS_H_take(tid, prevVal, val)] := pendingAsyncMultiset[PendingAsync_CAS_H_take(tid, prevVal, val)] + 1;
    return;
}



function {:constructor} PendingAsync_CAS_H_steal(tid: Tid, prevVal: int, val: int) : PendingAsync;

procedure {:inline 1} AddPendingAsync_CAS_H_steal(tid: Tid, prevVal: int, val: int);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_CAS_H_steal(tid: Tid, prevVal: int, val: int)
{

  L:
    pendingAsyncMultiset[PendingAsync_CAS_H_steal(tid, prevVal, val)] := pendingAsyncMultiset[PendingAsync_CAS_H_steal(tid, prevVal, val)] + 1;
    return;
}



procedure {:inline 1} atomic_readH_take_1(tid: Tid) returns (y: int);
  modifies take_in_cs, h_ss;



procedure {:inline 1} atomic_readH_steal_1(tid: Tid) returns (y: int);
  modifies h_ss;



procedure {:inline 1} atomic_readT_take_init_1(tid: Tid) returns (y: int);



procedure {:inline 1} atomic_readT_put_1(tid: Tid) returns (y: int);
  modifies put_in_cs;



procedure {:inline 1} atomic_readT_steal_1(tid: Tid) returns (y: int);
  modifies t_ss, steal_in_cs;



procedure {:inline 1} atomic_readItems_1(tid: Tid, ind: int) returns (y: int, b: bool);



procedure {:inline 1} atomic_writeT_put_1(tid: Tid, val: int);
  modifies T, put_in_cs;



procedure {:inline 1} atomic_writeT_take_1(tid: Tid, val: int);
  modifies T, t_ss;



procedure {:inline 1} atomic_writeT_take_abort_1(tid: Tid, val: int);
  modifies T, take_in_cs;



procedure {:inline 1} atomic_writeT_take_eq_1(tid: Tid, val: int);
  modifies T;



procedure {:inline 1} atomic_takeExitCS_1(tid: Tid);
  modifies take_in_cs;



procedure {:inline 1} atomic_stealExitCS_1(tid: Tid);
  modifies steal_in_cs;



procedure {:inline 1} atomic_writeItems_1(tid: Tid, idx: int, val: int);
  modifies items, status;



procedure {:inline 1} atomic_writeItems_put_1(tid: Tid, idx: int, val: int);
  modifies items, status;



procedure {:inline 1} atomic_CAS_H_take_1(tid: Tid, prevVal: int, val: int) returns (result: bool);
  modifies status, H, take_in_cs;



procedure {:inline 1} atomic_CAS_H_steal_1(tid: Tid, prevVal: int, val: int) returns (result: bool);
  modifies status, H, steal_in_cs;



implementation {:inline 1} atomic_readH_take_1(tid: Tid) returns (y: int)
{
  /*** structured program:
    assert tid == ptTid;
    y := H;
    take_in_cs := true;
    h_ss[tid] := H;
  **** end structured program */

  anon0:
    y := H;
    take_in_cs := true;
    h_ss[tid] := H;
    return;
}



implementation {:inline 1} atomic_readH_steal_1(tid: Tid) returns (y: int)
{
  /*** structured program:
    assert stealerTid(tid);
    assert !steal_in_cs[tid];
    y := H;
    h_ss[tid] := H;
  **** end structured program */

  anon0:
    y := H;
    h_ss[tid] := H;
    return;
}



implementation {:inline 1} atomic_readT_take_init_1(tid: Tid) returns (y: int)
{
  /*** structured program:
    assert tid != NIL;
    assert tid == ptTid;
    y := T;
  **** end structured program */

  anon0:
    y := T;
    return;
}



implementation {:inline 1} atomic_readT_put_1(tid: Tid) returns (y: int)
{
  /*** structured program:
    assert tid != NIL;
    assert tid == ptTid;
    put_in_cs := true;
    y := T;
  **** end structured program */

  anon0:
    put_in_cs := true;
    y := T;
    return;
}



implementation {:inline 1} atomic_readT_steal_1(tid: Tid) returns (y: int)
{
  /*** structured program:
    assert tid != NIL;
    assert stealerTid(tid);
    assert !steal_in_cs[tid];
    y := T;
    t_ss[tid] := T;
    steal_in_cs[tid] := true;
  **** end structured program */

  anon0:
    y := T;
    t_ss[tid] := T;
    steal_in_cs[tid] := true;
    return;
}



implementation {:inline 1} atomic_readItems_1(tid: Tid, ind: int) returns (y: int, b: bool)
{
  /*** structured program:
    y := items[ind];
    b := status[ind];
  **** end structured program */

  anon0:
    y := items[ind];
    b := status[ind];
    return;
}



implementation {:inline 1} atomic_writeT_put_1(tid: Tid, val: int)
{
  /*** structured program:
    assert tid == ptTid;
    T := T + 1;
    put_in_cs := false;
  **** end structured program */

  anon0:
    T := T + 1;
    put_in_cs := false;
    return;
}



implementation {:inline 1} atomic_writeT_take_1(tid: Tid, val: int)
{
  /*** structured program:
    assert tid == ptTid;
    T := val;
    t_ss[tid] := val;
  **** end structured program */

  anon0:
    T := val;
    t_ss[tid] := val;
    return;
}



implementation {:inline 1} atomic_writeT_take_abort_1(tid: Tid, val: int)
{
  /*** structured program:
    assert tid == ptTid;
    assert take_in_cs;
    T := val;
    take_in_cs := false;
  **** end structured program */

  anon0:
    T := val;
    take_in_cs := false;
    return;
}



implementation {:inline 1} atomic_writeT_take_eq_1(tid: Tid, val: int)
{
  /*** structured program:
    assert tid == ptTid;
    T := val;
  **** end structured program */

  anon0:
    T := val;
    return;
}



implementation {:inline 1} atomic_takeExitCS_1(tid: Tid)
{
  /*** structured program:
    assert tid == ptTid;
    take_in_cs := false;
  **** end structured program */

  anon0:
    take_in_cs := false;
    return;
}



implementation {:inline 1} atomic_stealExitCS_1(tid: Tid)
{
  /*** structured program:
    assert stealerTid(tid);
    assert steal_in_cs[tid];
    steal_in_cs[tid] := false;
  **** end structured program */

  anon0:
    steal_in_cs[tid] := false;
    return;
}



implementation {:inline 1} atomic_writeItems_1(tid: Tid, idx: int, val: int)
{
  /*** structured program:
    assert tid == ptTid;
    assert val != EMPTY;
    items[idx] := val;
    status[idx] := IN_Q;
  **** end structured program */

  anon0:
    items[idx] := val;
    status[idx] := IN_Q;
    return;
}



implementation {:inline 1} atomic_writeItems_put_1(tid: Tid, idx: int, val: int)
{
  /*** structured program:
    assert tid == ptTid;
    assert val != EMPTY;
    items[idx] := val;
    status[idx] := IN_Q;
  **** end structured program */

  anon0:
    items[idx] := val;
    status[idx] := IN_Q;
    return;
}



implementation {:inline 1} atomic_CAS_H_take_1(tid: Tid, prevVal: int, val: int) returns (result: bool)
{
  /*** structured program:
    assert tid == ptTid;
    if (H == prevVal)
    {
        status[H] := NOT_IN_Q;
        H := H + 1;
        result := true;
        take_in_cs := false;
    }
    else
    {
        result := false;
        take_in_cs := false;
    }
  **** end structured program */

  anon0:
    goto anon3_Then, anon3_Else;

  anon3_Else:
    assume {:partition} H != prevVal;
    result := false;
    take_in_cs := false;
    return;

  anon3_Then:
    assume {:partition} H == prevVal;
    status[H] := NOT_IN_Q;
    H := H + 1;
    result := true;
    take_in_cs := false;
    return;
}



implementation {:inline 1} atomic_CAS_H_steal_1(tid: Tid, prevVal: int, val: int) returns (result: bool)
{
  /*** structured program:
    assert stealerTid(tid);
    if (H == prevVal)
    {
        status[H] := NOT_IN_Q;
        H := H + 1;
        result := true;
        steal_in_cs[tid] := false;
    }
    else
    {
        result := false;
        steal_in_cs[tid] := false;
    }
  **** end structured program */

  anon0:
    goto anon3_Then, anon3_Else;

  anon3_Else:
    assume {:partition} H != prevVal;
    result := false;
    steal_in_cs[tid] := false;
    return;

  anon3_Then:
    assume {:partition} H == prevVal;
    status[H] := NOT_IN_Q;
    H := H + 1;
    result := true;
    steal_in_cs[tid] := false;
    return;
}



procedure {:inline 1} atomic_readH_take_3(tid: Tid) returns (y: int);
  modifies take_in_cs, h_ss;



procedure {:inline 1} atomic_readH_steal_3(tid: Tid) returns (y: int);
  modifies h_ss;



procedure {:inline 1} atomic_readT_take_init_3(tid: Tid) returns (y: int);



procedure {:inline 1} atomic_readT_put_3(tid: Tid) returns (y: int);
  modifies put_in_cs;



procedure {:inline 1} atomic_readT_steal_3(tid: Tid) returns (y: int);
  modifies t_ss, steal_in_cs;



procedure {:inline 1} atomic_readItems_3(tid: Tid, ind: int) returns (y: int, b: bool);



procedure {:inline 1} atomic_writeT_put_3(tid: Tid, val: int);
  modifies T, put_in_cs;



procedure {:inline 1} atomic_writeT_take_3(tid: Tid, val: int);
  modifies T, t_ss;



procedure {:inline 1} atomic_writeT_take_abort_3(tid: Tid, val: int);
  modifies T, take_in_cs;



procedure {:inline 1} atomic_writeT_take_eq_3(tid: Tid, val: int);
  modifies T;



procedure {:inline 1} atomic_takeExitCS_3(tid: Tid);
  modifies take_in_cs;



procedure {:inline 1} atomic_stealExitCS_3(tid: Tid);
  modifies steal_in_cs;



procedure {:inline 1} atomic_writeItems_3(tid: Tid, idx: int, val: int);
  modifies items, status;



procedure {:inline 1} atomic_writeItems_put_3(tid: Tid, idx: int, val: int);
  modifies items, status;



procedure {:inline 1} atomic_CAS_H_take_3(tid: Tid, prevVal: int, val: int) returns (result: bool);
  modifies status, H, take_in_cs;



procedure {:inline 1} atomic_CAS_H_steal_3(tid: Tid, prevVal: int, val: int) returns (result: bool);
  modifies status, H, steal_in_cs;



implementation {:inline 1} atomic_readH_take_3(tid: Tid) returns (y: int)
{
  /*** structured program:
    assert tid == ptTid;
    y := H;
    take_in_cs := true;
    h_ss[tid] := H;
  **** end structured program */

  anon0:
    y := H;
    take_in_cs := true;
    h_ss[tid] := H;
    return;
}



implementation {:inline 1} atomic_readH_steal_3(tid: Tid) returns (y: int)
{
  /*** structured program:
    assert stealerTid(tid);
    assert !steal_in_cs[tid];
    y := H;
    h_ss[tid] := H;
  **** end structured program */

  anon0:
    y := H;
    h_ss[tid] := H;
    return;
}



implementation {:inline 1} atomic_readT_take_init_3(tid: Tid) returns (y: int)
{
  /*** structured program:
    assert tid != NIL;
    assert tid == ptTid;
    y := T;
  **** end structured program */

  anon0:
    y := T;
    return;
}



implementation {:inline 1} atomic_readT_put_3(tid: Tid) returns (y: int)
{
  /*** structured program:
    assert tid != NIL;
    assert tid == ptTid;
    put_in_cs := true;
    y := T;
  **** end structured program */

  anon0:
    put_in_cs := true;
    y := T;
    return;
}



implementation {:inline 1} atomic_readT_steal_3(tid: Tid) returns (y: int)
{
  /*** structured program:
    assert tid != NIL;
    assert stealerTid(tid);
    assert !steal_in_cs[tid];
    y := T;
    t_ss[tid] := T;
    steal_in_cs[tid] := true;
  **** end structured program */

  anon0:
    y := T;
    t_ss[tid] := T;
    steal_in_cs[tid] := true;
    return;
}



implementation {:inline 1} atomic_readItems_3(tid: Tid, ind: int) returns (y: int, b: bool)
{
  /*** structured program:
    y := items[ind];
    b := status[ind];
  **** end structured program */

  anon0:
    y := items[ind];
    b := status[ind];
    return;
}



implementation {:inline 1} atomic_writeT_put_3(tid: Tid, val: int)
{
  /*** structured program:
    assert tid == ptTid;
    T := T + 1;
    put_in_cs := false;
  **** end structured program */

  anon0:
    T := T + 1;
    put_in_cs := false;
    return;
}



implementation {:inline 1} atomic_writeT_take_3(tid: Tid, val: int)
{
  /*** structured program:
    assert tid == ptTid;
    T := val;
    t_ss[tid] := val;
  **** end structured program */

  anon0:
    T := val;
    t_ss[tid] := val;
    return;
}



implementation {:inline 1} atomic_writeT_take_abort_3(tid: Tid, val: int)
{
  /*** structured program:
    assert tid == ptTid;
    assert take_in_cs;
    T := val;
    take_in_cs := false;
  **** end structured program */

  anon0:
    T := val;
    take_in_cs := false;
    return;
}



implementation {:inline 1} atomic_writeT_take_eq_3(tid: Tid, val: int)
{
  /*** structured program:
    assert tid == ptTid;
    T := val;
  **** end structured program */

  anon0:
    T := val;
    return;
}



implementation {:inline 1} atomic_takeExitCS_3(tid: Tid)
{
  /*** structured program:
    assert tid == ptTid;
    take_in_cs := false;
  **** end structured program */

  anon0:
    take_in_cs := false;
    return;
}



implementation {:inline 1} atomic_stealExitCS_3(tid: Tid)
{
  /*** structured program:
    assert stealerTid(tid);
    assert steal_in_cs[tid];
    steal_in_cs[tid] := false;
  **** end structured program */

  anon0:
    steal_in_cs[tid] := false;
    return;
}



implementation {:inline 1} atomic_writeItems_3(tid: Tid, idx: int, val: int)
{
  /*** structured program:
    assert tid == ptTid;
    assert val != EMPTY;
    items[idx] := val;
    status[idx] := IN_Q;
  **** end structured program */

  anon0:
    items[idx] := val;
    status[idx] := IN_Q;
    return;
}



implementation {:inline 1} atomic_writeItems_put_3(tid: Tid, idx: int, val: int)
{
  /*** structured program:
    assert tid == ptTid;
    assert val != EMPTY;
    items[idx] := val;
    status[idx] := IN_Q;
  **** end structured program */

  anon0:
    items[idx] := val;
    status[idx] := IN_Q;
    return;
}



implementation {:inline 1} atomic_CAS_H_take_3(tid: Tid, prevVal: int, val: int) returns (result: bool)
{
  /*** structured program:
    assert tid == ptTid;
    if (H == prevVal)
    {
        status[H] := NOT_IN_Q;
        H := H + 1;
        result := true;
        take_in_cs := false;
    }
    else
    {
        result := false;
        take_in_cs := false;
    }
  **** end structured program */

  anon0:
    goto anon3_Then, anon3_Else;

  anon3_Else:
    assume {:partition} H != prevVal;
    result := false;
    take_in_cs := false;
    return;

  anon3_Then:
    assume {:partition} H == prevVal;
    status[H] := NOT_IN_Q;
    H := H + 1;
    result := true;
    take_in_cs := false;
    return;
}



implementation {:inline 1} atomic_CAS_H_steal_3(tid: Tid, prevVal: int, val: int) returns (result: bool)
{
  /*** structured program:
    assert stealerTid(tid);
    if (H == prevVal)
    {
        status[H] := NOT_IN_Q;
        H := H + 1;
        result := true;
        steal_in_cs[tid] := false;
    }
    else
    {
        result := false;
        steal_in_cs[tid] := false;
    }
  **** end structured program */

  anon0:
    goto anon3_Then, anon3_Else;

  anon3_Else:
    assume {:partition} H != prevVal;
    result := false;
    steal_in_cs[tid] := false;
    return;

  anon3_Then:
    assume {:partition} H == prevVal;
    status[H] := NOT_IN_Q;
    H := H + 1;
    result := true;
    steal_in_cs[tid] := false;
    return;
}



procedure {:inline 1} atomic_put_4(tid: Tid, task: int);
  modifies status;



procedure {:inline 1} atomic_take_4(tid: Tid) returns (task: int, taskstatus: bool);
  modifies status;



procedure {:inline 1} atomic_steal_4(tid: Tid) returns (task: int, taskstatus: bool);
  modifies status;



implementation {:inline 1} atomic_put_4(tid: Tid, task: int)
{
  var i: int;

  /*** structured program:
    assume status[i] <==> NOT_IN_Q;
    status[i] := IN_Q;
  **** end structured program */

  anon0:
    assume status[i] <==> NOT_IN_Q;
    status[i] := IN_Q;
    return;
}



implementation {:inline 1} atomic_take_4(tid: Tid) returns (task: int, taskstatus: bool)
{
  var i: int;

  /*** structured program:
    if (*)
    {
        assume status[i] <==> IN_Q;
        status[i] := NOT_IN_Q;
    }
  **** end structured program */

  anon0:
    goto anon2_Then, anon2_Else;

  anon2_Else:
    return;

  anon2_Then:
    assume status[i] <==> IN_Q;
    status[i] := NOT_IN_Q;
    return;
}



implementation {:inline 1} atomic_steal_4(tid: Tid) returns (task: int, taskstatus: bool)
{
  var i: int;

  /*** structured program:
    if (*)
    {
        assume status[i] <==> IN_Q;
        status[i] := NOT_IN_Q;
    }
  **** end structured program */

  anon0:
    goto anon2_Then, anon2_Else;

  anon2_Else:
    return;

  anon2_Then:
    assume status[i] <==> IN_Q;
    status[i] := NOT_IN_Q;
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

procedure put_0(tid: Tid, task: int);
  modifies H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;



procedure take_0(tid: Tid) returns (task: int, taskstatus: bool);
  modifies H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;



procedure steal_0(tid: Tid) returns (task: int, taskstatus: bool);
  modifies H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;



procedure readH_take_0(tid: Tid) returns (y: int);
  modifies H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;



procedure readH_steal_0(tid: Tid) returns (y: int);
  modifies H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;



procedure readT_take_init_0(tid: Tid) returns (y: int);
  modifies H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;



procedure readT_put_0(tid: Tid) returns (y: int);
  modifies H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;



procedure readT_steal_0(tid: Tid) returns (y: int);
  modifies H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;



procedure readItems_0(tid: Tid, ind: int) returns (y: int, b: bool);
  modifies H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;



procedure writeT_put_0(tid: Tid, val: int);
  modifies H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;



procedure writeT_take_0(tid: Tid, val: int);
  modifies H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;



procedure writeT_take_abort_0(tid: Tid, val: int);
  modifies H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;



procedure writeT_take_eq_0(tid: Tid, val: int);
  modifies H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;



procedure takeExitCS_0(tid: Tid);
  modifies H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;



procedure stealExitCS_0(tid: Tid);
  modifies H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;



procedure writeItems_0(tid: Tid, idx: int, val: int);
  modifies H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;



procedure writeItems_put_0(tid: Tid, idx: int, val: int);
  modifies H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;



procedure CAS_H_take_0(tid: Tid, prevVal: int, val: int) returns (result: bool);
  modifies H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;



procedure CAS_H_steal_0(tid: Tid, prevVal: int, val: int) returns (result: bool);
  modifies H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;



implementation put_0(tid: Tid, task: int)
{
  var t: int;
  var oldH: int;
  var oldT: int;
  var oldStatusT: bool;
  var og_global_old_H: int;
  var og_global_old_T: int;
  var og_global_old_items: [int]int;
  var og_global_old_status: [int]bool;
  var og_global_old_take_in_cs: bool;
  var og_global_old_put_in_cs: bool;
  var og_global_old_steal_in_cs: [Tid]bool;
  var og_global_old_h_ss: [Tid]int;
  var og_global_old_t_ss: [Tid]int;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_tid_available: [Tid]bool;

  /*** structured program:
    call oldH, oldT := GhostRead();
    yield;
    assert {:expand} queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && !take_in_cs
       && !put_in_cs;
    assert {:expand} {:expand} ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert oldH <= H && oldT == T;
    assert {:expand} emptyInv(put_in_cs, take_in_cs, items, status, T);
    call t := readT_put(tid);
    call oldH, oldT := GhostRead();
    yield;
    assert {:expand} queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && !take_in_cs
       && put_in_cs;
    assert {:expand} ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert tid == ptTid && t == T;
    assert oldH <= H && oldT == T;
    assert (forall i: int :: i >= T ==> (status[i] <==> NOT_IN_Q) && items[i] == EMPTY);
    call writeItems_put(tid, t, task);
    call oldH, oldT := GhostRead();
    call oldStatusT := GhostReadStatus();
    yield;
    assert {:expand} queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T)
       && t == T
       && tid == ptTid
       && !take_in_cs
       && put_in_cs;
    assert {:expand} ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert items[t] == task;
    assert oldH <= H && oldT == T;
    assert (forall i: int :: i > T ==> (status[i] <==> NOT_IN_Q) && items[i] == EMPTY);
    call writeT_put(tid, t + 1);
    call oldH, oldT := GhostRead();
    yield;
    assert {:expand} queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && !take_in_cs
       && !put_in_cs;
    assert {:expand} ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert T == t + 1;
    assert oldH <= H && oldT == T;
    assert {:expand} emptyInv(put_in_cs, take_in_cs, items, status, T);
  **** end structured program */

  og_init:
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
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

  anon037:
    return;

  anon033:
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon037, CallToYieldProc;

  anon027:
    call writeT_put_0(tid, t + 1);
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
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
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon033, CallToYieldProc;

  anon023:
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon027, CallToYieldProc;

  anon016:
    call writeItems_put_0(tid, t, task);
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
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
    goto anon023, CallToYieldProc;

  anon012:
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon016, CallToYieldProc;

  anon06:
    call t := readT_put_0(tid);
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
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
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon012, CallToYieldProc;

  anon02:
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon06, CallToYieldProc;

  CallToYieldProc:
    call og_yield_0(linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation take_0(tid: Tid) returns (task: int, taskstatus: bool)
{
  var h: int;
  var t: int;
  var chk: bool;
  var oldH: int;
  var oldT: int;
  var og_global_old_H: int;
  var og_global_old_T: int;
  var og_global_old_items: [int]int;
  var og_global_old_status: [int]bool;
  var og_global_old_take_in_cs: bool;
  var og_global_old_put_in_cs: bool;
  var og_global_old_steal_in_cs: [Tid]bool;
  var og_global_old_h_ss: [Tid]int;
  var og_global_old_t_ss: [Tid]int;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_tid_available: [Tid]bool;

  /*** structured program:
    call oldH, oldT := GhostRead();
    yield;
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && !take_in_cs
       && !put_in_cs;
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert oldH <= H && oldT == T;
    while (true)
      invariant queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
         && tid == ptTid
         && !take_in_cs
         && !put_in_cs;
      invariant ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    {
        call oldH, oldT := GhostRead();
        yield;
        assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
           && tid == ptTid
           && !take_in_cs
           && !put_in_cs;
        assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
        assert oldH <= H && oldT == T;
        call t := readT_take_init(tid);
        call oldH, oldT := GhostRead();
        yield;
        assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
           && tid == ptTid
           && !take_in_cs
           && !put_in_cs;
        assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
        assert t == T;
        assert items[t - 1] == EMPTY ==> H > t - 1;
        assert oldH <= H && oldT == T;
        t := t - 1;
        call writeT_take(tid, t);
        call oldH, oldT := GhostRead();
        yield;
        assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T)
           && tid == ptTid
           && !take_in_cs
           && !put_in_cs
           && t_ss[tid] == t;
        assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
        assert t == T;
        assert items[t] == EMPTY ==> H > t;
        assert oldH <= H && oldT == T;
        call h := readH_take(tid);
        call oldH, oldT := GhostRead();
        yield;
        assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T)
           && tid == ptTid
           && take_in_cs
           && !put_in_cs
           && h_ss[tid] == h
           && t_ss[tid] == t;
        assert {:expand} ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
        assert t == T;
        assert h <= H;
        assert items[t] == EMPTY ==> H > t;
        assert oldH <= H;
        assert oldT == T;
        assert h <= H;
        assert oldH == h;
        if (t < h)
        {
            call writeT_take_abort(tid, h);
            task := EMPTY;
            call oldH, oldT := GhostRead();
            yield;
            assert h <= H;
            assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
               && tid == ptTid
               && !take_in_cs
               && !put_in_cs;
            assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
            assert h == T;
            assert oldH <= H && oldT == T;
            return;
        }

        call task, taskstatus := readItems(tid, t);
        call oldH, oldT := GhostRead();
        yield;
        assert H >= h;
        assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T)
           && tid == ptTid
           && take_in_cs
           && h_ss[tid] == h
           && t_ss[tid] == t;
        assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
        assert t == T && task == items[T];
        assert T > H ==> items[T] != EMPTY;
        assert oldH <= H && oldT == T && !put_in_cs && take_in_cs;
        if (t > h)
        {
            call takeExitCS(tid);
            call oldH, oldT := GhostRead();
            yield;
            assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
               && tid == ptTid
               && !take_in_cs
               && h_ss[tid] == h
               && t_ss[tid] == t;
            assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
            assert t == T && task == items[t] && task != EMPTY && (taskstatus <==> IN_Q);
            assert oldH <= H && oldT == T && !put_in_cs && !take_in_cs;
            return;
        }

        call writeT_take_eq(tid, h + 1);
        call oldH, oldT := GhostRead();
        yield;
        assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
           && tid == ptTid
           && h_ss[tid] == h
           && t_ss[tid] == t;
        assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
        assert T == h + 1;
        assert oldH <= H;
        assert oldT == T;
        assert task == items[t];
        assert !put_in_cs;
        call chk := CAS_H_take(tid, h, h + 1);
        call oldH, oldT := GhostRead();
        yield;
        assert chk ==> h + 1 == oldH && h_ss[tid] == oldH - 1 && task != EMPTY;
        assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
           && tid == ptTid
           && h_ss[tid] == h
           && t_ss[tid] == t;
        assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
        assert h + 1 == T;
        assert task == items[t];
        assert !take_in_cs;
        assert !put_in_cs;
        assert oldH <= H && oldT == T;
        if (chk)
        {
            call oldH, oldT := GhostRead();
            yield;
            assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
               && tid == ptTid
               && h_ss[tid] == h
               && t_ss[tid] == t;
            assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
            assert h + 1 == T && task == items[t] && !take_in_cs && !put_in_cs;
            assert oldH <= H && oldT == T && task != EMPTY && (taskstatus <==> IN_Q);
            return;
        }

        call oldH, oldT := GhostRead();
        yield;
        assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
           && tid == ptTid
           && h_ss[tid] == h
           && t_ss[tid] == t;
        assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
        assert h + 1 == T && task == items[t] && !take_in_cs && !put_in_cs;
        assert oldH <= H && oldT == T;
    }

    call oldH, oldT := GhostRead();
    yield;
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T)
       && tid == ptTid
       && !put_in_cs;
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert oldH <= H && oldT == T;
  **** end structured program */

  og_init:
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
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

  anon9_LoopHead:
    assume linear_tid_available
       == linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false));
    assume H == og_global_old_H;
    assume T == og_global_old_T;
    assume items == og_global_old_items;
    assume status == og_global_old_status;
    assume take_in_cs == og_global_old_take_in_cs;
    assume put_in_cs == og_global_old_put_in_cs;
    assume steal_in_cs == og_global_old_steal_in_cs;
    assume h_ss == og_global_old_h_ss;
    assume t_ss == og_global_old_t_ss;
    assume pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon9_LoopDone, anon9_LoopBody;

  anon9_LoopBody:
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
    goto anon9_LoopBody2, CallToYieldProc;

  anon10_Else:
    assume {:partition} h <= t;
    goto anon3;

  anon3:
    goto anon30, CallToYieldProc;

  anon11_Else:
    assume {:partition} h >= t;
    goto anon5;

  anon5:
    goto anon50, CallToYieldProc;

  anon12_Else:
    assume {:partition} !chk;
    goto anon7;

  anon7:
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
    goto anon72, CallToYieldProc;

  anon12_Then:
    assume {:partition} chk;
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
    goto anon12_Then3, CallToYieldProc;

  anon11_Then:
    assume {:partition} t > h;
    goto anon11_Then1, CallToYieldProc;

  anon10_Then:
    assume {:partition} t < h;
    goto anon10_Then1, CallToYieldProc;

  anon9_LoopDone:
    assume {:partition} !true;
    goto anon8;

  anon8:
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
    goto anon82, CallToYieldProc;

  anon06:
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    goto anon9_LoopHead;

  anon02:
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon06, CallToYieldProc;

  anon9_LoopBody33:
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon10_Then, anon10_Else;

  anon9_LoopBody27:
    call h := readH_take_0(tid);
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
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
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon9_LoopBody33, CallToYieldProc;

  anon9_LoopBody23:
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon9_LoopBody27, CallToYieldProc;

  anon9_LoopBody17:
    call writeT_take_0(tid, t);
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
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
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon9_LoopBody23, CallToYieldProc;

  anon9_LoopBody12:
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    t := t - 1;
    goto anon9_LoopBody17, CallToYieldProc;

  anon9_LoopBody6:
    call t := readT_take_init_0(tid);
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
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
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon9_LoopBody12, CallToYieldProc;

  anon9_LoopBody2:
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon9_LoopBody6, CallToYieldProc;

  anon36:
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon11_Then, anon11_Else;

  anon30:
    call task, taskstatus := readItems_0(tid, t);
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
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
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon36, CallToYieldProc;

  anon516:
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon12_Then, anon12_Else;

  anon510:
    call chk := CAS_H_take_0(tid, h, h + 1);
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
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
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon516, CallToYieldProc;

  anon56:
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon510, CallToYieldProc;

  anon50:
    call writeT_take_eq_0(tid, h + 1);
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
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
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon56, CallToYieldProc;

  anon76:
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    goto anon9_LoopHead;

  anon72:
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon76, CallToYieldProc;

  anon12_Then7:
    return;

  anon12_Then3:
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon12_Then7, CallToYieldProc;

  anon11_Then11:
    return;

  anon11_Then7:
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon11_Then11, CallToYieldProc;

  anon11_Then1:
    call takeExitCS_0(tid);
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
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
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon11_Then7, CallToYieldProc;

  anon10_Then12:
    return;

  anon10_Then8:
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon10_Then12, CallToYieldProc;

  anon10_Then1:
    call writeT_take_abort_0(tid, h);
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    task := EMPTY;
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
    goto anon10_Then8, CallToYieldProc;

  anon86:
    return;

  anon82:
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon86, CallToYieldProc;

  CallToYieldProc:
    call og_yield_0(linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation steal_0(tid: Tid) returns (task: int, taskstatus: bool)
{
  var h: int;
  var t: int;
  var chk: bool;
  var oldH: int;
  var oldT: int;
  var og_global_old_H: int;
  var og_global_old_T: int;
  var og_global_old_items: [int]int;
  var og_global_old_status: [int]bool;
  var og_global_old_take_in_cs: bool;
  var og_global_old_put_in_cs: bool;
  var og_global_old_steal_in_cs: [Tid]bool;
  var og_global_old_h_ss: [Tid]int;
  var og_global_old_t_ss: [Tid]int;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_tid_available: [Tid]bool;

  /*** structured program:
    call oldH, oldT := GhostRead();
    yield;
    assert stealerTid(tid);
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert oldH <= H;
    assert !steal_in_cs[tid];
    while (true)
      invariant stealerTid(tid);
      invariant queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
      invariant ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
      invariant !steal_in_cs[tid];
    {
        call oldH, oldT := GhostRead();
        yield;
        assert stealerTid(tid);
        assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
        assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
        assert oldH <= H;
        assert !steal_in_cs[tid];
        call h := readH_steal(tid);
        call oldH, oldT := GhostRead();
        yield;
        assert H >= h;
        assert !steal_in_cs[tid];
        assert h_ss[tid] == h;
        assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
        assert {:expand} ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
        assert oldH <= H;
        call t := readT_steal(tid);
        call oldH, oldT := GhostRead();
        yield;
        assert steal_in_cs[tid];
        assert stealerTid(tid) && H >= h && steal_in_cs[tid] && h_ss[tid] == h;
        assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
        assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
        assert oldH <= H && t == t_ss[tid];
        assert h < t && take_in_cs && h_ss[ptTid] < t_ss[ptTid] && h == H ==> H < T;
        assert H >= h;
        if (h >= t)
        {
            task := EMPTY;
            call stealExitCS(tid);
            call oldH, oldT := GhostRead();
            yield;
            assert !steal_in_cs[tid];
            assert stealerTid(tid) && !steal_in_cs[tid] && h_ss[tid] == h;
            assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
            assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
            assert oldH <= H;
            return;
        }

        call task, taskstatus := readItems(tid, h);
        call oldH, oldT := GhostRead();
        yield;
        assert stealerTid(tid) && steal_in_cs[tid] && h_ss[tid] == h;
        assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
        assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
        assert oldH <= H;
        assert oldH == H && H == h && h_ss[tid] == h ==> task != EMPTY;
        assert take_in_cs && h_ss[ptTid] < t_ss[ptTid] && h == H ==> H < T;
        assert h == H ==> (status[H] <==> IN_Q);
        call chk := CAS_H_steal(tid, h, h + 1);
        call oldH, oldT := GhostRead();
        yield;
        assert h_ss[tid] == h;
        assert chk
           ==> h + 1 == oldH && h_ss[tid] == h && task != EMPTY && (taskstatus <==> IN_Q);
        assert take_in_cs && h_ss[ptTid] < t_ss[ptTid] && chk ==> oldH - 1 < T;
        assert {:expand} ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
        assert stealerTid(tid) && !steal_in_cs[tid];
        assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
        assert oldH <= H;
        if (chk)
        {
            call oldH, oldT := GhostRead();
            yield;
            assert stealerTid(tid) && !steal_in_cs[tid];
            assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
            assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
            assert oldH <= H && task != EMPTY;
            return;
        }
    }

    call oldH, oldT := GhostRead();
    yield;
    assert chk && task != EMPTY;
    assert stealerTid(tid) && !steal_in_cs[tid];
    assert oldH <= H;
  **** end structured program */

  og_init:
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
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

  anon6_LoopHead:
    assume linear_tid_available
       == linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false));
    assume H == og_global_old_H;
    assume T == og_global_old_T;
    assume items == og_global_old_items;
    assume status == og_global_old_status;
    assume take_in_cs == og_global_old_take_in_cs;
    assume put_in_cs == og_global_old_put_in_cs;
    assume steal_in_cs == og_global_old_steal_in_cs;
    assume h_ss == og_global_old_h_ss;
    assume t_ss == og_global_old_t_ss;
    assume pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon6_LoopDone, anon6_LoopBody;

  anon6_LoopBody:
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
    goto anon6_LoopBody2, CallToYieldProc;

  anon7_Else:
    assume {:partition} t > h;
    goto anon3;

  anon3:
    goto anon30, CallToYieldProc;

  anon8_Else:
    assume {:partition} !chk;
    goto anon8_Else1, CallToYieldProc;

  anon8_Then:
    assume {:partition} chk;
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
    goto anon8_Then3, CallToYieldProc;

  anon7_Then:
    assume {:partition} h >= t;
    task := EMPTY;
    goto anon7_Then2, CallToYieldProc;

  anon6_LoopDone:
    assume {:partition} !true;
    goto anon5;

  anon5:
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
    goto anon52, CallToYieldProc;

  anon06:
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    goto anon6_LoopHead;

  anon02:
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon06, CallToYieldProc;

  anon6_LoopBody22:
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon7_Then, anon7_Else;

  anon6_LoopBody16:
    call t := readT_steal_0(tid);
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
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
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon6_LoopBody22, CallToYieldProc;

  anon6_LoopBody12:
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon6_LoopBody16, CallToYieldProc;

  anon6_LoopBody6:
    call h := readH_steal_0(tid);
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
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
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon6_LoopBody12, CallToYieldProc;

  anon6_LoopBody2:
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon6_LoopBody6, CallToYieldProc;

  anon316:
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon8_Then, anon8_Else;

  anon310:
    call chk := CAS_H_steal_0(tid, h, h + 1);
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
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
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon316, CallToYieldProc;

  anon36:
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon310, CallToYieldProc;

  anon30:
    call task, taskstatus := readItems_0(tid, h);
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
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
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon36, CallToYieldProc;

  anon8_Else1:
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    goto anon6_LoopHead;

  anon8_Then7:
    return;

  anon8_Then3:
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon8_Then7, CallToYieldProc;

  anon7_Then12:
    return;

  anon7_Then8:
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon7_Then12, CallToYieldProc;

  anon7_Then2:
    call stealExitCS_0(tid);
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
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
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon7_Then8, CallToYieldProc;

  anon56:
    return;

  anon52:
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    goto anon56, CallToYieldProc;

  CallToYieldProc:
    call og_yield_0(linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



procedure {:inline 1} Impl_YieldChecker_put_0(linear_tid_in: [Tid]bool, 
    og_global_old_H: int, 
    og_global_old_T: int, 
    og_global_old_items: [int]int, 
    og_global_old_status: [int]bool, 
    og_global_old_take_in_cs: bool, 
    og_global_old_put_in_cs: bool, 
    og_global_old_steal_in_cs: [Tid]bool, 
    og_global_old_h_ss: [Tid]int, 
    og_global_old_t_ss: [Tid]int, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_take_0(linear_tid_in: [Tid]bool, 
    og_global_old_H: int, 
    og_global_old_T: int, 
    og_global_old_items: [int]int, 
    og_global_old_status: [int]bool, 
    og_global_old_take_in_cs: bool, 
    og_global_old_put_in_cs: bool, 
    og_global_old_steal_in_cs: [Tid]bool, 
    og_global_old_h_ss: [Tid]int, 
    og_global_old_t_ss: [Tid]int, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_steal_0(linear_tid_in: [Tid]bool, 
    og_global_old_H: int, 
    og_global_old_T: int, 
    og_global_old_items: [int]int, 
    og_global_old_status: [int]bool, 
    og_global_old_take_in_cs: bool, 
    og_global_old_put_in_cs: bool, 
    og_global_old_steal_in_cs: [Tid]bool, 
    og_global_old_h_ss: [Tid]int, 
    og_global_old_t_ss: [Tid]int, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



implementation {:inline 1} Impl_YieldChecker_put_0(linear_tid_in: [Tid]bool, 
    og_global_old_H: int, 
    og_global_old_T: int, 
    og_global_old_items: [int]int, 
    og_global_old_status: [int]bool, 
    og_global_old_take_in_cs: bool, 
    og_global_old_put_in_cs: bool, 
    og_global_old_steal_in_cs: [Tid]bool, 
    og_global_old_h_ss: [Tid]int, 
    og_global_old_t_ss: [Tid]int, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var t: int;
  var oldH: int;
  var oldT: int;
  var oldStatusT: bool;
  var tid: Tid;
  var task: int;
  var og_local_old_H: int;
  var og_local_old_T: int;
  var og_local_old_items: [int]int;
  var og_local_old_status: [int]bool;
  var og_local_old_take_in_cs: bool;
  var og_local_old_put_in_cs: bool;
  var og_local_old_steal_in_cs: [Tid]bool;
  var og_local_old_h_ss: [Tid]int;
  var og_local_old_t_ss: [Tid]int;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0, L1, L2, L3;

  exit:
    return;

  L0:
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

  L2:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume false;
    return;

  L3:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_take_0(linear_tid_in: [Tid]bool, 
    og_global_old_H: int, 
    og_global_old_T: int, 
    og_global_old_items: [int]int, 
    og_global_old_status: [int]bool, 
    og_global_old_take_in_cs: bool, 
    og_global_old_put_in_cs: bool, 
    og_global_old_steal_in_cs: [Tid]bool, 
    og_global_old_h_ss: [Tid]int, 
    og_global_old_t_ss: [Tid]int, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var h: int;
  var t: int;
  var chk: bool;
  var oldH: int;
  var oldT: int;
  var tid: Tid;
  var task: int;
  var taskstatus: bool;
  var og_local_old_H: int;
  var og_local_old_T: int;
  var og_local_old_items: [int]int;
  var og_local_old_status: [int]bool;
  var og_local_old_take_in_cs: bool;
  var og_local_old_put_in_cs: bool;
  var og_local_old_steal_in_cs: [Tid]bool;
  var og_local_old_h_ss: [Tid]int;
  var og_local_old_t_ss: [Tid]int;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11, L12;

  exit:
    return;

  L0:
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

  L2:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume false;
    return;

  L3:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume false;
    return;

  L4:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume false;
    return;

  L5:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume false;
    return;

  L6:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume false;
    return;

  L7:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume false;
    return;

  L8:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume false;
    return;

  L9:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume false;
    return;

  L10:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume false;
    return;

  L11:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume false;
    return;

  L12:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_steal_0(linear_tid_in: [Tid]bool, 
    og_global_old_H: int, 
    og_global_old_T: int, 
    og_global_old_items: [int]int, 
    og_global_old_status: [int]bool, 
    og_global_old_take_in_cs: bool, 
    og_global_old_put_in_cs: bool, 
    og_global_old_steal_in_cs: [Tid]bool, 
    og_global_old_h_ss: [Tid]int, 
    og_global_old_t_ss: [Tid]int, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var h: int;
  var t: int;
  var chk: bool;
  var oldH: int;
  var oldT: int;
  var tid: Tid;
  var task: int;
  var taskstatus: bool;
  var og_local_old_H: int;
  var og_local_old_T: int;
  var og_local_old_items: [int]int;
  var og_local_old_status: [int]bool;
  var og_local_old_take_in_cs: bool;
  var og_local_old_put_in_cs: bool;
  var og_local_old_steal_in_cs: [Tid]bool;
  var og_local_old_h_ss: [Tid]int;
  var og_local_old_t_ss: [Tid]int;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0, L1, L2, L3, L4, L5, L6, L7, L8;

  exit:
    return;

  L0:
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

  L2:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume false;
    return;

  L3:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume false;
    return;

  L4:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume false;
    return;

  L5:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume false;
    return;

  L6:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume false;
    return;

  L7:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume false;
    return;

  L8:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume false;
    return;
}



procedure {:inline 1} og_yield_0(linear_tid_in: [Tid]bool, 
    og_global_old_H: int, 
    og_global_old_T: int, 
    og_global_old_items: [int]int, 
    og_global_old_status: [int]bool, 
    og_global_old_take_in_cs: bool, 
    og_global_old_put_in_cs: bool, 
    og_global_old_steal_in_cs: [Tid]bool, 
    og_global_old_h_ss: [Tid]int, 
    og_global_old_t_ss: [Tid]int, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



implementation {:inline 1} og_yield_0(linear_tid_in: [Tid]bool, 
    og_global_old_H: int, 
    og_global_old_T: int, 
    og_global_old_items: [int]int, 
    og_global_old_status: [int]bool, 
    og_global_old_take_in_cs: bool, 
    og_global_old_put_in_cs: bool, 
    og_global_old_steal_in_cs: [Tid]bool, 
    og_global_old_h_ss: [Tid]int, 
    og_global_old_t_ss: [Tid]int, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{

  enter:
    goto L_0, L_1, L_2;

  L_0:
    call Impl_YieldChecker_put_0(linear_tid_in, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset);
    return;

  L_1:
    call Impl_YieldChecker_take_0(linear_tid_in, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset);
    return;

  L_2:
    call Impl_YieldChecker_steal_0(linear_tid_in, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset);
    return;
}



procedure put_3(tid: Tid, task: int);
  requires {:expand} queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
     && tid == ptTid
     && task != EMPTY
     && !take_in_cs
     && !put_in_cs;
  requires {:expand} ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
  requires {:expand} emptyInv(put_in_cs, take_in_cs, items, status, T);
  modifies H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
  ensures {:expand} queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
     && tid == ptTid
     && !take_in_cs
     && !put_in_cs;
  ensures {:expand} ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
  ensures {:expand} emptyInv(put_in_cs, take_in_cs, items, status, T);



procedure take_3(tid: Tid) returns (task: int, taskstatus: bool);
  requires {:expand} queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
     && tid == ptTid
     && !take_in_cs
     && !put_in_cs;
  requires {:expand} ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
  modifies H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
  ensures queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
     && tid == ptTid
     && !take_in_cs
     && !put_in_cs
     && (task != EMPTY ==> (taskstatus <==> IN_Q));
  ensures ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);



procedure steal_3(tid: Tid) returns (task: int, taskstatus: bool);
  requires queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
     && stealerTid(tid)
     && !steal_in_cs[tid];
  requires ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
  modifies H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
  ensures queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
     && !steal_in_cs[tid]
     && (task != EMPTY ==> (taskstatus <==> IN_Q));
  ensures ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);



implementation put_3(tid: Tid, task: int)
{
  var t: int;
  var oldH: int;
  var oldT: int;
  var oldStatusT: bool;
  var og_global_old_H: int;
  var og_global_old_T: int;
  var og_global_old_items: [int]int;
  var og_global_old_status: [int]bool;
  var og_global_old_take_in_cs: bool;
  var og_global_old_put_in_cs: bool;
  var og_global_old_steal_in_cs: [Tid]bool;
  var og_global_old_h_ss: [Tid]int;
  var og_global_old_t_ss: [Tid]int;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;
  var linear_tid_available: [Tid]bool;

  /*** structured program:
    call oldH, oldT := GhostRead();
    yield;
    assert {:expand} queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && !take_in_cs
       && !put_in_cs;
    assert {:expand} {:expand} ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert oldH <= H && oldT == T;
    assert {:expand} emptyInv(put_in_cs, take_in_cs, items, status, T);
    call t := readT_put(tid);
    call oldH, oldT := GhostRead();
    yield;
    assert {:expand} queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && !take_in_cs
       && put_in_cs;
    assert {:expand} ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert tid == ptTid && t == T;
    assert oldH <= H && oldT == T;
    assert (forall i: int :: i >= T ==> (status[i] <==> NOT_IN_Q) && items[i] == EMPTY);
    call writeItems_put(tid, t, task);
    call oldH, oldT := GhostRead();
    call oldStatusT := GhostReadStatus();
    yield;
    assert {:expand} queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T)
       && t == T
       && tid == ptTid
       && !take_in_cs
       && put_in_cs;
    assert {:expand} ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert items[t] == task;
    assert oldH <= H && oldT == T;
    assert (forall i: int :: i > T ==> (status[i] <==> NOT_IN_Q) && items[i] == EMPTY);
    call writeT_put(tid, t + 1);
    call oldH, oldT := GhostRead();
    yield;
    assert {:expand} queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && !take_in_cs
       && !put_in_cs;
    assert {:expand} ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert T == t + 1;
    assert oldH <= H && oldT == T;
    assert {:expand} emptyInv(put_in_cs, take_in_cs, items, status, T);
  **** end structured program */

  og_init:
    og_pc, og_ok, linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := false, false, linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    goto anon0;

  anon0:
    call oldH, oldT := GhostRead();
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
    assert {:expand} queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && !take_in_cs
       && !put_in_cs;
    assert {:expand} {:expand} ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert oldH <= H && oldT == T;
    assert {:expand} emptyInv(put_in_cs, take_in_cs, items, status, T);
    goto anon07, CallToYieldProc;

  anon0101:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (og_global_old_status[#tmp_0_second_i] <==> NOT_IN_Q));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (og_global_old_status[#tmp_0_second_i] <==> NOT_IN_Q));
    assert og_ok;
    return;

  anon088:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (og_global_old_status[#tmp_0_second_i] <==> NOT_IN_Q));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (og_global_old_status[#tmp_0_second_i] <==> NOT_IN_Q));
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume og_pc || true;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && !take_in_cs
       && !put_in_cs;
    assume ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assume T == t + 1;
    assume oldH <= H && oldT == T;
    assume emptyInv(put_in_cs, take_in_cs, items, status, T);
    goto anon0101, CallToYieldProc;

  anon062:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (og_global_old_status[#tmp_0_second_i] <==> NOT_IN_Q));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (og_global_old_status[#tmp_0_second_i] <==> NOT_IN_Q));
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume og_pc || true;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T)
       && t == T
       && tid == ptTid
       && !take_in_cs
       && put_in_cs;
    assume ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assume items[t] == task;
    assume oldH <= H && oldT == T;
    assume (forall i: int :: i > T ==> (status[i] <==> NOT_IN_Q) && items[i] == EMPTY);
    // <<< injected gate
    assert tid == ptTid;
    // injected gate >>>
    call atomic_writeT_put_3(tid, t + 1);
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    call oldH, oldT := GhostRead();
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
    assert {:expand} queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && !take_in_cs
       && !put_in_cs;
    assert {:expand} ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert T == t + 1;
    assert oldH <= H && oldT == T;
    assert {:expand} emptyInv(put_in_cs, take_in_cs, items, status, T);
    goto anon088, CallToYieldProc;

  anon033:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (og_global_old_status[#tmp_0_second_i] <==> NOT_IN_Q));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (og_global_old_status[#tmp_0_second_i] <==> NOT_IN_Q));
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume og_pc || true;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && !take_in_cs
       && put_in_cs;
    assume ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assume tid == ptTid && t == T;
    assume oldH <= H && oldT == T;
    assume (forall i: int :: i >= T ==> (status[i] <==> NOT_IN_Q) && items[i] == EMPTY);
    // <<< injected gate
    assert tid == ptTid;
    assert task != EMPTY;
    // injected gate >>>
    call atomic_writeItems_put_3(tid, t, task);
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    call oldH, oldT := GhostRead();
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    call oldStatusT := GhostReadStatus();
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
    assert {:expand} queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T)
       && t == T
       && tid == ptTid
       && !take_in_cs
       && put_in_cs;
    assert {:expand} ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert items[t] == task;
    assert oldH <= H && oldT == T;
    assert (forall i: int :: i > T ==> (status[i] <==> NOT_IN_Q) && items[i] == EMPTY);
    goto anon062, CallToYieldProc;

  anon07:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (og_global_old_status[#tmp_0_second_i] <==> NOT_IN_Q));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && (og_global_old_status[#tmp_0_second_i] <==> NOT_IN_Q));
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume og_pc || true;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && !take_in_cs
       && !put_in_cs;
    assume ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assume oldH <= H && oldT == T;
    assume emptyInv(put_in_cs, take_in_cs, items, status, T);
    // <<< injected gate
    assert tid != NIL;
    assert tid == ptTid;
    // injected gate >>>
    call t := atomic_readT_put_3(tid);
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    call oldH, oldT := GhostRead();
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
    assert {:expand} queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && !take_in_cs
       && put_in_cs;
    assert {:expand} ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert tid == ptTid && t == T;
    assert oldH <= H && oldT == T;
    assert (forall i: int :: i >= T ==> (status[i] <==> NOT_IN_Q) && items[i] == EMPTY);
    goto anon033, CallToYieldProc;

  CallToYieldProc:
    call og_yield_3(linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation take_3(tid: Tid) returns (task: int, taskstatus: bool)
{
  var h: int;
  var t: int;
  var chk: bool;
  var oldH: int;
  var oldT: int;
  var og_global_old_H: int;
  var og_global_old_T: int;
  var og_global_old_items: [int]int;
  var og_global_old_status: [int]bool;
  var og_global_old_take_in_cs: bool;
  var og_global_old_put_in_cs: bool;
  var og_global_old_steal_in_cs: [Tid]bool;
  var og_global_old_h_ss: [Tid]int;
  var og_global_old_t_ss: [Tid]int;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;
  var og_old_task: int;
  var og_old_taskstatus: bool;
  var linear_tid_available: [Tid]bool;
  var og_pc_anon9_LoopHead: bool;
  var og_ok_anon9_LoopHead: bool;

  /*** structured program:
    call oldH, oldT := GhostRead();
    yield;
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && !take_in_cs
       && !put_in_cs;
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert oldH <= H && oldT == T;
    while (true)
      invariant queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
         && tid == ptTid
         && !take_in_cs
         && !put_in_cs;
      invariant ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    {
        call oldH, oldT := GhostRead();
        yield;
        assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
           && tid == ptTid
           && !take_in_cs
           && !put_in_cs;
        assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
        assert oldH <= H && oldT == T;
        call t := readT_take_init(tid);
        call oldH, oldT := GhostRead();
        yield;
        assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
           && tid == ptTid
           && !take_in_cs
           && !put_in_cs;
        assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
        assert t == T;
        assert items[t - 1] == EMPTY ==> H > t - 1;
        assert oldH <= H && oldT == T;
        t := t - 1;
        call writeT_take(tid, t);
        call oldH, oldT := GhostRead();
        yield;
        assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T)
           && tid == ptTid
           && !take_in_cs
           && !put_in_cs
           && t_ss[tid] == t;
        assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
        assert t == T;
        assert items[t] == EMPTY ==> H > t;
        assert oldH <= H && oldT == T;
        call h := readH_take(tid);
        call oldH, oldT := GhostRead();
        yield;
        assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T)
           && tid == ptTid
           && take_in_cs
           && !put_in_cs
           && h_ss[tid] == h
           && t_ss[tid] == t;
        assert {:expand} ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
        assert t == T;
        assert h <= H;
        assert items[t] == EMPTY ==> H > t;
        assert oldH <= H;
        assert oldT == T;
        assert h <= H;
        assert oldH == h;
        if (t < h)
        {
            call writeT_take_abort(tid, h);
            task := EMPTY;
            call oldH, oldT := GhostRead();
            yield;
            assert h <= H;
            assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
               && tid == ptTid
               && !take_in_cs
               && !put_in_cs;
            assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
            assert h == T;
            assert oldH <= H && oldT == T;
            return;
        }

        call task, taskstatus := readItems(tid, t);
        call oldH, oldT := GhostRead();
        yield;
        assert H >= h;
        assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T)
           && tid == ptTid
           && take_in_cs
           && h_ss[tid] == h
           && t_ss[tid] == t;
        assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
        assert t == T && task == items[T];
        assert T > H ==> items[T] != EMPTY;
        assert oldH <= H && oldT == T && !put_in_cs && take_in_cs;
        if (t > h)
        {
            call takeExitCS(tid);
            call oldH, oldT := GhostRead();
            yield;
            assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
               && tid == ptTid
               && !take_in_cs
               && h_ss[tid] == h
               && t_ss[tid] == t;
            assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
            assert t == T && task == items[t] && task != EMPTY && (taskstatus <==> IN_Q);
            assert oldH <= H && oldT == T && !put_in_cs && !take_in_cs;
            return;
        }

        call writeT_take_eq(tid, h + 1);
        call oldH, oldT := GhostRead();
        yield;
        assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
           && tid == ptTid
           && h_ss[tid] == h
           && t_ss[tid] == t;
        assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
        assert T == h + 1;
        assert oldH <= H;
        assert oldT == T;
        assert task == items[t];
        assert !put_in_cs;
        call chk := CAS_H_take(tid, h, h + 1);
        call oldH, oldT := GhostRead();
        yield;
        assert chk ==> h + 1 == oldH && h_ss[tid] == oldH - 1 && task != EMPTY;
        assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
           && tid == ptTid
           && h_ss[tid] == h
           && t_ss[tid] == t;
        assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
        assert h + 1 == T;
        assert task == items[t];
        assert !take_in_cs;
        assert !put_in_cs;
        assert oldH <= H && oldT == T;
        if (chk)
        {
            call oldH, oldT := GhostRead();
            yield;
            assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
               && tid == ptTid
               && h_ss[tid] == h
               && t_ss[tid] == t;
            assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
            assert h + 1 == T && task == items[t] && !take_in_cs && !put_in_cs;
            assert oldH <= H && oldT == T && task != EMPTY && (taskstatus <==> IN_Q);
            return;
        }

        call oldH, oldT := GhostRead();
        yield;
        assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
           && tid == ptTid
           && h_ss[tid] == h
           && t_ss[tid] == t;
        assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
        assert h + 1 == T && task == items[t] && !take_in_cs && !put_in_cs;
        assert oldH <= H && oldT == T;
    }

    call oldH, oldT := GhostRead();
    yield;
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T)
       && tid == ptTid
       && !put_in_cs;
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert oldH <= H && oldT == T;
  **** end structured program */

  og_init:
    og_pc, og_pc_anon9_LoopHead, og_ok, og_ok_anon9_LoopHead, linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset, og_old_task, og_old_taskstatus := false, false, false, false, linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset, task, taskstatus;
    goto anon0;

  anon0:
    call oldH, oldT := GhostRead();
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
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && !take_in_cs
       && !put_in_cs;
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert oldH <= H && oldT == T;
    goto anon06, CallToYieldProc;

  anon9_LoopHead:
    assert og_pc_anon9_LoopHead == og_pc;
    assert og_ok_anon9_LoopHead ==> og_ok;
    assume linear_tid_available
       == linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false));
    assume H == og_global_old_H;
    assume T == og_global_old_T;
    assume items == og_global_old_items;
    assume status == og_global_old_status;
    assume take_in_cs == og_global_old_take_in_cs;
    assume put_in_cs == og_global_old_put_in_cs;
    assume steal_in_cs == og_global_old_steal_in_cs;
    assume h_ss == og_global_old_h_ss;
    assume t_ss == og_global_old_t_ss;
    assume pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assume task == og_old_task;
    assume taskstatus == og_old_taskstatus;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && !take_in_cs
       && !put_in_cs;
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    goto anon9_LoopDone, anon9_LoopBody;

  anon9_LoopBody:
    call oldH, oldT := GhostRead();
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
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && !take_in_cs
       && !put_in_cs;
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert oldH <= H && oldT == T;
    goto anon9_LoopBody6, CallToYieldProc;

  anon10_Else:
    assume {:partition} h <= t;
    goto anon3;

  anon3:
    call task, taskstatus := atomic_readItems_3(tid, t);
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    call oldH, oldT := GhostRead();
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
    assert H >= h;
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T)
       && tid == ptTid
       && take_in_cs
       && h_ss[tid] == h
       && t_ss[tid] == t;
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert t == T && task == items[T];
    assert T > H ==> items[T] != EMPTY;
    assert oldH <= H && oldT == T && !put_in_cs && take_in_cs;
    goto anon311, CallToYieldProc;

  anon11_Else:
    assume {:partition} h >= t;
    goto anon5;

  anon5:
    // <<< injected gate
    assert tid == ptTid;
    // injected gate >>>
    call atomic_writeT_take_eq_3(tid, h + 1);
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    call oldH, oldT := GhostRead();
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
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && h_ss[tid] == h
       && t_ss[tid] == t;
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert T == h + 1;
    assert oldH <= H;
    assert oldT == T;
    assert task == items[t];
    assert !put_in_cs;
    goto anon515, CallToYieldProc;

  anon12_Else:
    assume {:partition} !chk;
    goto anon7;

  anon7:
    call oldH, oldT := GhostRead();
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
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && h_ss[tid] == h
       && t_ss[tid] == t;
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert h + 1 == T && task == items[t] && !take_in_cs && !put_in_cs;
    assert oldH <= H && oldT == T;
    goto anon77, CallToYieldProc;

  anon12_Then:
    assume {:partition} chk;
    call oldH, oldT := GhostRead();
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
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && h_ss[tid] == h
       && t_ss[tid] == t;
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert h + 1 == T && task == items[t] && !take_in_cs && !put_in_cs;
    assert oldH <= H && oldT == T && task != EMPTY && (taskstatus <==> IN_Q);
    goto anon12_Then8, CallToYieldProc;

  anon11_Then:
    assume {:partition} t > h;
    // <<< injected gate
    assert tid == ptTid;
    // injected gate >>>
    call atomic_takeExitCS_3(tid);
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    call oldH, oldT := GhostRead();
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
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && !take_in_cs
       && h_ss[tid] == h
       && t_ss[tid] == t;
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert t == T && task == items[t] && task != EMPTY && (taskstatus <==> IN_Q);
    assert oldH <= H && oldT == T && !put_in_cs && !take_in_cs;
    goto anon11_Then13, CallToYieldProc;

  anon10_Then:
    assume {:partition} t < h;
    // <<< injected gate
    assert tid == ptTid;
    assert take_in_cs;
    // injected gate >>>
    call atomic_writeT_take_abort_3(tid, h);
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    task := EMPTY;
    call oldH, oldT := GhostRead();
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
    assert h <= H;
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && !take_in_cs
       && !put_in_cs;
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert h == T;
    assert oldH <= H && oldT == T;
    goto anon10_Then16, CallToYieldProc;

  anon9_LoopDone:
    assume {:partition} !true;
    goto anon8;

  anon8:
    call oldH, oldT := GhostRead();
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
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T)
       && tid == ptTid
       && !put_in_cs;
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert oldH <= H && oldT == T;
    goto anon86, CallToYieldProc;

  anon017:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == og_old_task
         && (taskstatus <==> og_old_taskstatus);
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    og_pc_anon9_LoopHead, og_ok_anon9_LoopHead := og_pc, og_ok;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset, og_old_task, og_old_taskstatus := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset, task, taskstatus;
    goto anon9_LoopHead;

  anon06:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == og_old_task
         && (taskstatus <==> og_old_taskstatus);
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume og_pc || true;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset, og_old_task, og_old_taskstatus := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset, task, taskstatus;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && !take_in_cs
       && !put_in_cs;
    assume ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assume oldH <= H && oldT == T;
    goto anon017, CallToYieldProc;

  anon9_LoopBody88:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == og_old_task
         && (taskstatus <==> og_old_taskstatus);
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume og_pc || true;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset, og_old_task, og_old_taskstatus := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset, task, taskstatus;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T)
       && tid == ptTid
       && take_in_cs
       && !put_in_cs
       && h_ss[tid] == h
       && t_ss[tid] == t;
    assume ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assume t == T;
    assume h <= H;
    assume items[t] == EMPTY ==> H > t;
    assume oldH <= H;
    assume oldT == T;
    assume h <= H;
    assume oldH == h;
    goto anon10_Then, anon10_Else;

  anon9_LoopBody58:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == og_old_task
         && (taskstatus <==> og_old_taskstatus);
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume og_pc || true;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset, og_old_task, og_old_taskstatus := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset, task, taskstatus;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T)
       && tid == ptTid
       && !take_in_cs
       && !put_in_cs
       && t_ss[tid] == t;
    assume ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assume t == T;
    assume items[t] == EMPTY ==> H > t;
    assume oldH <= H && oldT == T;
    // <<< injected gate
    assert tid == ptTid;
    // injected gate >>>
    call h := atomic_readH_take_3(tid);
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    call oldH, oldT := GhostRead();
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
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T)
       && tid == ptTid
       && take_in_cs
       && !put_in_cs
       && h_ss[tid] == h
       && t_ss[tid] == t;
    assert {:expand} ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert t == T;
    assert h <= H;
    assert items[t] == EMPTY ==> H > t;
    assert oldH <= H;
    assert oldT == T;
    assert h <= H;
    assert oldH == h;
    goto anon9_LoopBody88, CallToYieldProc;

  anon9_LoopBody31:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == og_old_task
         && (taskstatus <==> og_old_taskstatus);
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume og_pc || true;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset, og_old_task, og_old_taskstatus := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset, task, taskstatus;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && !take_in_cs
       && !put_in_cs;
    assume ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assume t == T;
    assume items[t - 1] == EMPTY ==> H > t - 1;
    assume oldH <= H && oldT == T;
    t := t - 1;
    // <<< injected gate
    assert tid == ptTid;
    // injected gate >>>
    call atomic_writeT_take_3(tid, t);
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    call oldH, oldT := GhostRead();
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
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T)
       && tid == ptTid
       && !take_in_cs
       && !put_in_cs
       && t_ss[tid] == t;
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert t == T;
    assert items[t] == EMPTY ==> H > t;
    assert oldH <= H && oldT == T;
    goto anon9_LoopBody58, CallToYieldProc;

  anon9_LoopBody6:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == og_old_task
         && (taskstatus <==> og_old_taskstatus);
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume og_pc || true;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset, og_old_task, og_old_taskstatus := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset, task, taskstatus;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && !take_in_cs
       && !put_in_cs;
    assume ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assume oldH <= H && oldT == T;
    // <<< injected gate
    assert tid != NIL;
    assert tid == ptTid;
    // injected gate >>>
    call t := atomic_readT_take_init_3(tid);
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    call oldH, oldT := GhostRead();
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
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && !take_in_cs
       && !put_in_cs;
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert t == T;
    assert items[t - 1] == EMPTY ==> H > t - 1;
    assert oldH <= H && oldT == T;
    goto anon9_LoopBody31, CallToYieldProc;

  anon311:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == og_old_task
         && (taskstatus <==> og_old_taskstatus);
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume og_pc || true;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset, og_old_task, og_old_taskstatus := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset, task, taskstatus;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume H >= h;
    assume queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T)
       && tid == ptTid
       && take_in_cs
       && h_ss[tid] == h
       && t_ss[tid] == t;
    assume ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assume t == T && task == items[T];
    assume T > H ==> items[T] != EMPTY;
    assume oldH <= H && oldT == T && !put_in_cs && take_in_cs;
    goto anon11_Then, anon11_Else;

  anon546:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == og_old_task
         && (taskstatus <==> og_old_taskstatus);
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume og_pc || true;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset, og_old_task, og_old_taskstatus := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset, task, taskstatus;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume chk ==> h + 1 == oldH && h_ss[tid] == oldH - 1 && task != EMPTY;
    assume queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && h_ss[tid] == h
       && t_ss[tid] == t;
    assume ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assume h + 1 == T;
    assume task == items[t];
    assume !take_in_cs;
    assume !put_in_cs;
    assume oldH <= H && oldT == T;
    goto anon12_Then, anon12_Else;

  anon515:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == og_old_task
         && (taskstatus <==> og_old_taskstatus);
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume og_pc || true;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset, og_old_task, og_old_taskstatus := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset, task, taskstatus;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && h_ss[tid] == h
       && t_ss[tid] == t;
    assume ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assume T == h + 1;
    assume oldH <= H;
    assume oldT == T;
    assume task == items[t];
    assume !put_in_cs;
    // <<< injected gate
    assert tid == ptTid;
    // injected gate >>>
    call chk := atomic_CAS_H_take_3(tid, h, h + 1);
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    call oldH, oldT := GhostRead();
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
    assert chk ==> h + 1 == oldH && h_ss[tid] == oldH - 1 && task != EMPTY;
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && h_ss[tid] == h
       && t_ss[tid] == t;
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert h + 1 == T;
    assert task == items[t];
    assert !take_in_cs;
    assert !put_in_cs;
    assert oldH <= H && oldT == T;
    goto anon546, CallToYieldProc;

  anon719:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == og_old_task
         && (taskstatus <==> og_old_taskstatus);
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset, og_old_task, og_old_taskstatus := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset, task, taskstatus;
    goto anon9_LoopHead;

  anon77:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == og_old_task
         && (taskstatus <==> og_old_taskstatus);
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume og_pc || true;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset, og_old_task, og_old_taskstatus := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset, task, taskstatus;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && h_ss[tid] == h
       && t_ss[tid] == t;
    assume ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assume h + 1 == T && task == items[t] && !take_in_cs && !put_in_cs;
    assume oldH <= H && oldT == T;
    goto anon719, CallToYieldProc;

  anon12_Then20:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == og_old_task
         && (taskstatus <==> og_old_taskstatus);
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_ok;
    return;

  anon12_Then8:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == og_old_task
         && (taskstatus <==> og_old_taskstatus);
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume og_pc || true;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset, og_old_task, og_old_taskstatus := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset, task, taskstatus;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && h_ss[tid] == h
       && t_ss[tid] == t;
    assume ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assume h + 1 == T && task == items[t] && !take_in_cs && !put_in_cs;
    assume oldH <= H && oldT == T && task != EMPTY && (taskstatus <==> IN_Q);
    goto anon12_Then20, CallToYieldProc;

  anon11_Then25:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == og_old_task
         && (taskstatus <==> og_old_taskstatus);
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_ok;
    return;

  anon11_Then13:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == og_old_task
         && (taskstatus <==> og_old_taskstatus);
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume og_pc || true;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset, og_old_task, og_old_taskstatus := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset, task, taskstatus;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && !take_in_cs
       && h_ss[tid] == h
       && t_ss[tid] == t;
    assume ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assume t == T && task == items[t] && task != EMPTY && (taskstatus <==> IN_Q);
    assume oldH <= H && oldT == T && !put_in_cs && !take_in_cs;
    goto anon11_Then25, CallToYieldProc;

  anon10_Then29:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == og_old_task
         && (taskstatus <==> og_old_taskstatus);
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_ok;
    return;

  anon10_Then16:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == og_old_task
         && (taskstatus <==> og_old_taskstatus);
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume og_pc || true;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset, og_old_task, og_old_taskstatus := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset, task, taskstatus;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume h <= H;
    assume queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && !take_in_cs
       && !put_in_cs;
    assume ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assume h == T;
    assume oldH <= H && oldT == T;
    goto anon10_Then29, CallToYieldProc;

  anon817:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == og_old_task
         && (taskstatus <==> og_old_taskstatus);
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_ok;
    return;

  anon86:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == og_old_task
         && (taskstatus <==> og_old_taskstatus);
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume og_pc || true;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset, og_old_task, og_old_taskstatus := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset, task, taskstatus;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T)
       && tid == ptTid
       && !put_in_cs;
    assume ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assume oldH <= H && oldT == T;
    goto anon817, CallToYieldProc;

  CallToYieldProc:
    call og_yield_3(linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation steal_3(tid: Tid) returns (task: int, taskstatus: bool)
{
  var h: int;
  var t: int;
  var chk: bool;
  var oldH: int;
  var oldT: int;
  var og_global_old_H: int;
  var og_global_old_T: int;
  var og_global_old_items: [int]int;
  var og_global_old_status: [int]bool;
  var og_global_old_take_in_cs: bool;
  var og_global_old_put_in_cs: bool;
  var og_global_old_steal_in_cs: [Tid]bool;
  var og_global_old_h_ss: [Tid]int;
  var og_global_old_t_ss: [Tid]int;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;
  var og_old_task: int;
  var og_old_taskstatus: bool;
  var linear_tid_available: [Tid]bool;
  var og_pc_anon6_LoopHead: bool;
  var og_ok_anon6_LoopHead: bool;

  /*** structured program:
    call oldH, oldT := GhostRead();
    yield;
    assert stealerTid(tid);
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert oldH <= H;
    assert !steal_in_cs[tid];
    while (true)
      invariant stealerTid(tid);
      invariant queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
      invariant ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
      invariant !steal_in_cs[tid];
    {
        call oldH, oldT := GhostRead();
        yield;
        assert stealerTid(tid);
        assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
        assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
        assert oldH <= H;
        assert !steal_in_cs[tid];
        call h := readH_steal(tid);
        call oldH, oldT := GhostRead();
        yield;
        assert H >= h;
        assert !steal_in_cs[tid];
        assert h_ss[tid] == h;
        assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
        assert {:expand} ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
        assert oldH <= H;
        call t := readT_steal(tid);
        call oldH, oldT := GhostRead();
        yield;
        assert steal_in_cs[tid];
        assert stealerTid(tid) && H >= h && steal_in_cs[tid] && h_ss[tid] == h;
        assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
        assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
        assert oldH <= H && t == t_ss[tid];
        assert h < t && take_in_cs && h_ss[ptTid] < t_ss[ptTid] && h == H ==> H < T;
        assert H >= h;
        if (h >= t)
        {
            task := EMPTY;
            call stealExitCS(tid);
            call oldH, oldT := GhostRead();
            yield;
            assert !steal_in_cs[tid];
            assert stealerTid(tid) && !steal_in_cs[tid] && h_ss[tid] == h;
            assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
            assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
            assert oldH <= H;
            return;
        }

        call task, taskstatus := readItems(tid, h);
        call oldH, oldT := GhostRead();
        yield;
        assert stealerTid(tid) && steal_in_cs[tid] && h_ss[tid] == h;
        assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
        assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
        assert oldH <= H;
        assert oldH == H && H == h && h_ss[tid] == h ==> task != EMPTY;
        assert take_in_cs && h_ss[ptTid] < t_ss[ptTid] && h == H ==> H < T;
        assert h == H ==> (status[H] <==> IN_Q);
        call chk := CAS_H_steal(tid, h, h + 1);
        call oldH, oldT := GhostRead();
        yield;
        assert h_ss[tid] == h;
        assert chk
           ==> h + 1 == oldH && h_ss[tid] == h && task != EMPTY && (taskstatus <==> IN_Q);
        assert take_in_cs && h_ss[ptTid] < t_ss[ptTid] && chk ==> oldH - 1 < T;
        assert {:expand} ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
        assert stealerTid(tid) && !steal_in_cs[tid];
        assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
        assert oldH <= H;
        if (chk)
        {
            call oldH, oldT := GhostRead();
            yield;
            assert stealerTid(tid) && !steal_in_cs[tid];
            assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
            assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
            assert oldH <= H && task != EMPTY;
            return;
        }
    }

    call oldH, oldT := GhostRead();
    yield;
    assert chk && task != EMPTY;
    assert stealerTid(tid) && !steal_in_cs[tid];
    assert oldH <= H;
  **** end structured program */

  og_init:
    og_pc, og_pc_anon6_LoopHead, og_ok, og_ok_anon6_LoopHead, linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset, og_old_task, og_old_taskstatus := false, false, false, false, linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset, task, taskstatus;
    goto anon0;

  anon0:
    call oldH, oldT := GhostRead();
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
    assert stealerTid(tid);
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert oldH <= H;
    assert !steal_in_cs[tid];
    goto anon08, CallToYieldProc;

  anon6_LoopHead:
    assert og_pc_anon6_LoopHead == og_pc;
    assert og_ok_anon6_LoopHead ==> og_ok;
    assume linear_tid_available
       == linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false));
    assume H == og_global_old_H;
    assume T == og_global_old_T;
    assume items == og_global_old_items;
    assume status == og_global_old_status;
    assume take_in_cs == og_global_old_take_in_cs;
    assume put_in_cs == og_global_old_put_in_cs;
    assume steal_in_cs == og_global_old_steal_in_cs;
    assume h_ss == og_global_old_h_ss;
    assume t_ss == og_global_old_t_ss;
    assume pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assume task == og_old_task;
    assume taskstatus == og_old_taskstatus;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assert stealerTid(tid);
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert !steal_in_cs[tid];
    goto anon6_LoopDone, anon6_LoopBody;

  anon6_LoopBody:
    call oldH, oldT := GhostRead();
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
    assert stealerTid(tid);
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert oldH <= H;
    assert !steal_in_cs[tid];
    goto anon6_LoopBody8, CallToYieldProc;

  anon7_Else:
    assume {:partition} t > h;
    goto anon3;

  anon3:
    call task, taskstatus := atomic_readItems_3(tid, h);
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    call oldH, oldT := GhostRead();
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
    assert stealerTid(tid) && steal_in_cs[tid] && h_ss[tid] == h;
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert oldH <= H;
    assert oldH == H && H == h && h_ss[tid] == h ==> task != EMPTY;
    assert take_in_cs && h_ss[ptTid] < t_ss[ptTid] && h == H ==> H < T;
    assert h == H ==> (status[H] <==> IN_Q);
    goto anon312, CallToYieldProc;

  anon8_Else:
    assume {:partition} !chk;
    goto anon8_Else1, CallToYieldProc;

  anon8_Then:
    assume {:partition} chk;
    call oldH, oldT := GhostRead();
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
    assert stealerTid(tid) && !steal_in_cs[tid];
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert oldH <= H && task != EMPTY;
    goto anon8_Then8, CallToYieldProc;

  anon7_Then:
    assume {:partition} h >= t;
    task := EMPTY;
    // <<< injected gate
    assert stealerTid(tid);
    assert steal_in_cs[tid];
    // injected gate >>>
    call atomic_stealExitCS_3(tid);
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    call oldH, oldT := GhostRead();
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
    assert !steal_in_cs[tid];
    assert stealerTid(tid) && !steal_in_cs[tid] && h_ss[tid] == h;
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert oldH <= H;
    goto anon7_Then16, CallToYieldProc;

  anon6_LoopDone:
    assume {:partition} !true;
    goto anon5;

  anon5:
    call oldH, oldT := GhostRead();
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
    assert chk && task != EMPTY;
    assert stealerTid(tid) && !steal_in_cs[tid];
    assert oldH <= H;
    goto anon56, CallToYieldProc;

  anon021:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == og_old_task
         && (taskstatus <==> og_old_taskstatus);
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    og_pc_anon6_LoopHead, og_ok_anon6_LoopHead := og_pc, og_ok;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset, og_old_task, og_old_taskstatus := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset, task, taskstatus;
    goto anon6_LoopHead;

  anon08:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == og_old_task
         && (taskstatus <==> og_old_taskstatus);
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume og_pc || true;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset, og_old_task, og_old_taskstatus := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset, task, taskstatus;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume stealerTid(tid);
    assume queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
    assume ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assume oldH <= H;
    assume !steal_in_cs[tid];
    goto anon021, CallToYieldProc;

  anon6_LoopBody67:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == og_old_task
         && (taskstatus <==> og_old_taskstatus);
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume og_pc || true;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset, og_old_task, og_old_taskstatus := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset, task, taskstatus;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume steal_in_cs[tid];
    assume stealerTid(tid) && H >= h && steal_in_cs[tid] && h_ss[tid] == h;
    assume queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
    assume ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assume oldH <= H && t == t_ss[tid];
    assume h < t && take_in_cs && h_ss[ptTid] < t_ss[ptTid] && h == H ==> H < T;
    assume H >= h;
    goto anon7_Then, anon7_Else;

  anon6_LoopBody36:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == og_old_task
         && (taskstatus <==> og_old_taskstatus);
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume og_pc || true;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset, og_old_task, og_old_taskstatus := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset, task, taskstatus;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume H >= h;
    assume !steal_in_cs[tid];
    assume h_ss[tid] == h;
    assume queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
    assume ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assume oldH <= H;
    // <<< injected gate
    assert tid != NIL;
    assert stealerTid(tid);
    assert !steal_in_cs[tid];
    // injected gate >>>
    call t := atomic_readT_steal_3(tid);
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    call oldH, oldT := GhostRead();
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
    assert steal_in_cs[tid];
    assert stealerTid(tid) && H >= h && steal_in_cs[tid] && h_ss[tid] == h;
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert oldH <= H && t == t_ss[tid];
    assert h < t && take_in_cs && h_ss[ptTid] < t_ss[ptTid] && h == H ==> H < T;
    assert H >= h;
    goto anon6_LoopBody67, CallToYieldProc;

  anon6_LoopBody8:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == og_old_task
         && (taskstatus <==> og_old_taskstatus);
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume og_pc || true;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset, og_old_task, og_old_taskstatus := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset, task, taskstatus;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume stealerTid(tid);
    assume queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
    assume ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assume oldH <= H;
    assume !steal_in_cs[tid];
    // <<< injected gate
    assert stealerTid(tid);
    assert !steal_in_cs[tid];
    // injected gate >>>
    call h := atomic_readH_steal_3(tid);
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    call oldH, oldT := GhostRead();
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
    assert H >= h;
    assert !steal_in_cs[tid];
    assert h_ss[tid] == h;
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
    assert {:expand} ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert oldH <= H;
    goto anon6_LoopBody36, CallToYieldProc;

  anon342:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == og_old_task
         && (taskstatus <==> og_old_taskstatus);
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume og_pc || true;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset, og_old_task, og_old_taskstatus := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset, task, taskstatus;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume h_ss[tid] == h;
    assume chk
       ==> h + 1 == oldH && h_ss[tid] == h && task != EMPTY && (taskstatus <==> IN_Q);
    assume take_in_cs && h_ss[ptTid] < t_ss[ptTid] && chk ==> oldH - 1 < T;
    assume ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assume stealerTid(tid) && !steal_in_cs[tid];
    assume queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
    assume oldH <= H;
    goto anon8_Then, anon8_Else;

  anon312:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == og_old_task
         && (taskstatus <==> og_old_taskstatus);
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume og_pc || true;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset, og_old_task, og_old_taskstatus := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset, task, taskstatus;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume stealerTid(tid) && steal_in_cs[tid] && h_ss[tid] == h;
    assume queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
    assume ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assume oldH <= H;
    assume oldH == H && H == h && h_ss[tid] == h ==> task != EMPTY;
    assume take_in_cs && h_ss[ptTid] < t_ss[ptTid] && h == H ==> H < T;
    assume h == H ==> (status[H] <==> IN_Q);
    // <<< injected gate
    assert stealerTid(tid);
    // injected gate >>>
    call chk := atomic_CAS_H_steal_3(tid, h, h + 1);
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    call oldH, oldT := GhostRead();
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
    assert h_ss[tid] == h;
    assert chk
       ==> h + 1 == oldH && h_ss[tid] == h && task != EMPTY && (taskstatus <==> IN_Q);
    assert take_in_cs && h_ss[ptTid] < t_ss[ptTid] && chk ==> oldH - 1 < T;
    assert {:expand} ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert stealerTid(tid) && !steal_in_cs[tid];
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
    assert oldH <= H;
    goto anon342, CallToYieldProc;

  anon8_Else1:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == og_old_task
         && (taskstatus <==> og_old_taskstatus);
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset, og_old_task, og_old_taskstatus := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset, task, taskstatus;
    goto anon6_LoopHead;

  anon8_Then20:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == og_old_task
         && (taskstatus <==> og_old_taskstatus);
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_ok;
    return;

  anon8_Then8:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == og_old_task
         && (taskstatus <==> og_old_taskstatus);
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume og_pc || true;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset, og_old_task, og_old_taskstatus := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset, task, taskstatus;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume stealerTid(tid) && !steal_in_cs[tid];
    assume queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
    assume ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assume oldH <= H && task != EMPTY;
    goto anon8_Then20, CallToYieldProc;

  anon7_Then29:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == og_old_task
         && (taskstatus <==> og_old_taskstatus);
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_ok;
    return;

  anon7_Then16:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == og_old_task
         && (taskstatus <==> og_old_taskstatus);
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume og_pc || true;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset, og_old_task, og_old_taskstatus := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset, task, taskstatus;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume !steal_in_cs[tid];
    assume stealerTid(tid) && !steal_in_cs[tid] && h_ss[tid] == h;
    assume queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
    assume ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assume oldH <= H;
    goto anon7_Then29, CallToYieldProc;

  anon517:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == og_old_task
         && (taskstatus <==> og_old_taskstatus);
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_ok;
    return;

  anon56:
    assert og_pc
       || 
      (status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    assert og_pc
       ==> status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == og_old_task
         && (taskstatus <==> og_old_taskstatus);
    og_pc, og_ok := status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_i: int :: 
        status == og_global_old_status[#tmp_0_second_i := NOT_IN_Q]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && task == task
           && (taskstatus <==> taskstatus)
           && (og_global_old_status[#tmp_0_second_i] <==> IN_Q))
       || (
        status == og_global_old_status
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && task == task
         && (taskstatus <==> taskstatus));
    havoc H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset;
    assume og_pc || true;
    linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset, og_old_task, og_old_taskstatus := linear_tid_MapOr(TidCollector(tid), linear_tid_MapConstBool(false)), H, T, items, status, take_in_cs, put_in_cs, steal_in_cs, h_ss, t_ss, pendingAsyncMultiset, task, taskstatus;
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_hole, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume chk && task != EMPTY;
    assume stealerTid(tid) && !steal_in_cs[tid];
    assume oldH <= H;
    goto anon517, CallToYieldProc;

  CallToYieldProc:
    call og_yield_3(linear_tid_available, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



procedure {:inline 1} Impl_YieldChecker_put_3(linear_tid_in: [Tid]bool, 
    og_global_old_H: int, 
    og_global_old_T: int, 
    og_global_old_items: [int]int, 
    og_global_old_status: [int]bool, 
    og_global_old_take_in_cs: bool, 
    og_global_old_put_in_cs: bool, 
    og_global_old_steal_in_cs: [Tid]bool, 
    og_global_old_h_ss: [Tid]int, 
    og_global_old_t_ss: [Tid]int, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_take_3(linear_tid_in: [Tid]bool, 
    og_global_old_H: int, 
    og_global_old_T: int, 
    og_global_old_items: [int]int, 
    og_global_old_status: [int]bool, 
    og_global_old_take_in_cs: bool, 
    og_global_old_put_in_cs: bool, 
    og_global_old_steal_in_cs: [Tid]bool, 
    og_global_old_h_ss: [Tid]int, 
    og_global_old_t_ss: [Tid]int, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_steal_3(linear_tid_in: [Tid]bool, 
    og_global_old_H: int, 
    og_global_old_T: int, 
    og_global_old_items: [int]int, 
    og_global_old_status: [int]bool, 
    og_global_old_take_in_cs: bool, 
    og_global_old_put_in_cs: bool, 
    og_global_old_steal_in_cs: [Tid]bool, 
    og_global_old_h_ss: [Tid]int, 
    og_global_old_t_ss: [Tid]int, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



implementation {:inline 1} Impl_YieldChecker_put_3(linear_tid_in: [Tid]bool, 
    og_global_old_H: int, 
    og_global_old_T: int, 
    og_global_old_items: [int]int, 
    og_global_old_status: [int]bool, 
    og_global_old_take_in_cs: bool, 
    og_global_old_put_in_cs: bool, 
    og_global_old_steal_in_cs: [Tid]bool, 
    og_global_old_h_ss: [Tid]int, 
    og_global_old_t_ss: [Tid]int, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var t: int;
  var oldH: int;
  var oldT: int;
  var oldStatusT: bool;
  var tid: Tid;
  var task: int;
  var og_local_old_H: int;
  var og_local_old_T: int;
  var og_local_old_items: [int]int;
  var og_local_old_status: [int]bool;
  var og_local_old_take_in_cs: bool;
  var og_local_old_put_in_cs: bool;
  var og_local_old_steal_in_cs: [Tid]bool;
  var og_local_old_h_ss: [Tid]int;
  var og_local_old_t_ss: [Tid]int;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0, L1, L2, L3;

  exit:
    return;

  L0:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume queueInv(og_global_old_steal_in_cs, 
        og_global_old_put_in_cs, 
        og_global_old_take_in_cs, 
        og_global_old_items, 
        og_global_old_status, 
        og_global_old_H, 
        og_global_old_T - 1)
       && tid == ptTid
       && !og_global_old_take_in_cs
       && !og_global_old_put_in_cs;
    assume ideasInv(og_global_old_put_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_H, 
      og_global_old_T, 
      og_global_old_take_in_cs, 
      og_global_old_steal_in_cs, 
      og_global_old_h_ss, 
      og_global_old_t_ss);
    assume oldH <= og_global_old_H && oldT == og_global_old_T;
    assume emptyInv(og_global_old_put_in_cs, 
      og_global_old_take_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_T);
    assert {:expand} queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && !take_in_cs
       && !put_in_cs;
    assert {:expand} {:expand} ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert oldH <= H && oldT == T;
    assert {:expand} emptyInv(put_in_cs, take_in_cs, items, status, T);
    assume false;
    return;

  L1:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume queueInv(og_global_old_steal_in_cs, 
        og_global_old_put_in_cs, 
        og_global_old_take_in_cs, 
        og_global_old_items, 
        og_global_old_status, 
        og_global_old_H, 
        og_global_old_T - 1)
       && tid == ptTid
       && !og_global_old_take_in_cs
       && og_global_old_put_in_cs;
    assume ideasInv(og_global_old_put_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_H, 
      og_global_old_T, 
      og_global_old_take_in_cs, 
      og_global_old_steal_in_cs, 
      og_global_old_h_ss, 
      og_global_old_t_ss);
    assume tid == ptTid && t == og_global_old_T;
    assume oldH <= og_global_old_H && oldT == og_global_old_T;
    assume (forall i: int :: 
      i >= og_global_old_T
         ==> (og_global_old_status[i] <==> NOT_IN_Q) && og_global_old_items[i] == EMPTY);
    assert {:expand} queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && !take_in_cs
       && put_in_cs;
    assert {:expand} ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert tid == ptTid && t == T;
    assert oldH <= H && oldT == T;
    assert (forall i: int :: i >= T ==> (status[i] <==> NOT_IN_Q) && items[i] == EMPTY);
    assume false;
    return;

  L2:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume queueInv(og_global_old_steal_in_cs, 
        og_global_old_put_in_cs, 
        og_global_old_take_in_cs, 
        og_global_old_items, 
        og_global_old_status, 
        og_global_old_H, 
        og_global_old_T)
       && t == og_global_old_T
       && tid == ptTid
       && !og_global_old_take_in_cs
       && og_global_old_put_in_cs;
    assume ideasInv(og_global_old_put_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_H, 
      og_global_old_T, 
      og_global_old_take_in_cs, 
      og_global_old_steal_in_cs, 
      og_global_old_h_ss, 
      og_global_old_t_ss);
    assume og_global_old_items[t] == task;
    assume oldH <= og_global_old_H && oldT == og_global_old_T;
    assume (forall i: int :: 
      i > og_global_old_T
         ==> (og_global_old_status[i] <==> NOT_IN_Q) && og_global_old_items[i] == EMPTY);
    assert {:expand} queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T)
       && t == T
       && tid == ptTid
       && !take_in_cs
       && put_in_cs;
    assert {:expand} ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert items[t] == task;
    assert oldH <= H && oldT == T;
    assert (forall i: int :: i > T ==> (status[i] <==> NOT_IN_Q) && items[i] == EMPTY);
    assume false;
    return;

  L3:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume queueInv(og_global_old_steal_in_cs, 
        og_global_old_put_in_cs, 
        og_global_old_take_in_cs, 
        og_global_old_items, 
        og_global_old_status, 
        og_global_old_H, 
        og_global_old_T - 1)
       && tid == ptTid
       && !og_global_old_take_in_cs
       && !og_global_old_put_in_cs;
    assume ideasInv(og_global_old_put_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_H, 
      og_global_old_T, 
      og_global_old_take_in_cs, 
      og_global_old_steal_in_cs, 
      og_global_old_h_ss, 
      og_global_old_t_ss);
    assume og_global_old_T == t + 1;
    assume oldH <= og_global_old_H && oldT == og_global_old_T;
    assume emptyInv(og_global_old_put_in_cs, 
      og_global_old_take_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_T);
    assert {:expand} queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && !take_in_cs
       && !put_in_cs;
    assert {:expand} ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert T == t + 1;
    assert oldH <= H && oldT == T;
    assert {:expand} emptyInv(put_in_cs, take_in_cs, items, status, T);
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_take_3(linear_tid_in: [Tid]bool, 
    og_global_old_H: int, 
    og_global_old_T: int, 
    og_global_old_items: [int]int, 
    og_global_old_status: [int]bool, 
    og_global_old_take_in_cs: bool, 
    og_global_old_put_in_cs: bool, 
    og_global_old_steal_in_cs: [Tid]bool, 
    og_global_old_h_ss: [Tid]int, 
    og_global_old_t_ss: [Tid]int, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var h: int;
  var t: int;
  var chk: bool;
  var oldH: int;
  var oldT: int;
  var tid: Tid;
  var task: int;
  var taskstatus: bool;
  var og_local_old_H: int;
  var og_local_old_T: int;
  var og_local_old_items: [int]int;
  var og_local_old_status: [int]bool;
  var og_local_old_take_in_cs: bool;
  var og_local_old_put_in_cs: bool;
  var og_local_old_steal_in_cs: [Tid]bool;
  var og_local_old_h_ss: [Tid]int;
  var og_local_old_t_ss: [Tid]int;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11, L12;

  exit:
    return;

  L0:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume queueInv(og_global_old_steal_in_cs, 
        og_global_old_put_in_cs, 
        og_global_old_take_in_cs, 
        og_global_old_items, 
        og_global_old_status, 
        og_global_old_H, 
        og_global_old_T - 1)
       && tid == ptTid
       && !og_global_old_take_in_cs
       && !og_global_old_put_in_cs;
    assume ideasInv(og_global_old_put_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_H, 
      og_global_old_T, 
      og_global_old_take_in_cs, 
      og_global_old_steal_in_cs, 
      og_global_old_h_ss, 
      og_global_old_t_ss);
    assume oldH <= og_global_old_H && oldT == og_global_old_T;
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && !take_in_cs
       && !put_in_cs;
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert oldH <= H && oldT == T;
    assume false;
    return;

  L1:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume queueInv(og_global_old_steal_in_cs, 
        og_global_old_put_in_cs, 
        og_global_old_take_in_cs, 
        og_global_old_items, 
        og_global_old_status, 
        og_global_old_H, 
        og_global_old_T - 1)
       && tid == ptTid
       && !og_global_old_take_in_cs
       && !og_global_old_put_in_cs;
    assume ideasInv(og_global_old_put_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_H, 
      og_global_old_T, 
      og_global_old_take_in_cs, 
      og_global_old_steal_in_cs, 
      og_global_old_h_ss, 
      og_global_old_t_ss);
    assume oldH <= og_global_old_H && oldT == og_global_old_T;
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && !take_in_cs
       && !put_in_cs;
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert oldH <= H && oldT == T;
    assume false;
    return;

  L2:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume queueInv(og_global_old_steal_in_cs, 
        og_global_old_put_in_cs, 
        og_global_old_take_in_cs, 
        og_global_old_items, 
        og_global_old_status, 
        og_global_old_H, 
        og_global_old_T - 1)
       && tid == ptTid
       && !og_global_old_take_in_cs
       && !og_global_old_put_in_cs;
    assume ideasInv(og_global_old_put_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_H, 
      og_global_old_T, 
      og_global_old_take_in_cs, 
      og_global_old_steal_in_cs, 
      og_global_old_h_ss, 
      og_global_old_t_ss);
    assume t == og_global_old_T;
    assume og_global_old_items[t - 1] == EMPTY ==> og_global_old_H > t - 1;
    assume oldH <= og_global_old_H && oldT == og_global_old_T;
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && !take_in_cs
       && !put_in_cs;
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert t == T;
    assert items[t - 1] == EMPTY ==> H > t - 1;
    assert oldH <= H && oldT == T;
    assume false;
    return;

  L3:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume queueInv(og_global_old_steal_in_cs, 
        og_global_old_put_in_cs, 
        og_global_old_take_in_cs, 
        og_global_old_items, 
        og_global_old_status, 
        og_global_old_H, 
        og_global_old_T)
       && tid == ptTid
       && !og_global_old_take_in_cs
       && !og_global_old_put_in_cs
       && og_global_old_t_ss[tid] == t;
    assume ideasInv(og_global_old_put_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_H, 
      og_global_old_T, 
      og_global_old_take_in_cs, 
      og_global_old_steal_in_cs, 
      og_global_old_h_ss, 
      og_global_old_t_ss);
    assume t == og_global_old_T;
    assume og_global_old_items[t] == EMPTY ==> og_global_old_H > t;
    assume oldH <= og_global_old_H && oldT == og_global_old_T;
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T)
       && tid == ptTid
       && !take_in_cs
       && !put_in_cs
       && t_ss[tid] == t;
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert t == T;
    assert items[t] == EMPTY ==> H > t;
    assert oldH <= H && oldT == T;
    assume false;
    return;

  L4:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume queueInv(og_global_old_steal_in_cs, 
        og_global_old_put_in_cs, 
        og_global_old_take_in_cs, 
        og_global_old_items, 
        og_global_old_status, 
        og_global_old_H, 
        og_global_old_T)
       && tid == ptTid
       && og_global_old_take_in_cs
       && !og_global_old_put_in_cs
       && og_global_old_h_ss[tid] == h
       && og_global_old_t_ss[tid] == t;
    assume ideasInv(og_global_old_put_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_H, 
      og_global_old_T, 
      og_global_old_take_in_cs, 
      og_global_old_steal_in_cs, 
      og_global_old_h_ss, 
      og_global_old_t_ss);
    assume t == og_global_old_T;
    assume h <= og_global_old_H;
    assume og_global_old_items[t] == EMPTY ==> og_global_old_H > t;
    assume oldH <= og_global_old_H;
    assume oldT == og_global_old_T;
    assume h <= og_global_old_H;
    assume oldH == h;
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T)
       && tid == ptTid
       && take_in_cs
       && !put_in_cs
       && h_ss[tid] == h
       && t_ss[tid] == t;
    assert {:expand} ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert t == T;
    assert h <= H;
    assert items[t] == EMPTY ==> H > t;
    assert oldH <= H;
    assert oldT == T;
    assert h <= H;
    assert oldH == h;
    assume false;
    return;

  L5:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume og_global_old_H >= h;
    assume queueInv(og_global_old_steal_in_cs, 
        og_global_old_put_in_cs, 
        og_global_old_take_in_cs, 
        og_global_old_items, 
        og_global_old_status, 
        og_global_old_H, 
        og_global_old_T)
       && tid == ptTid
       && og_global_old_take_in_cs
       && og_global_old_h_ss[tid] == h
       && og_global_old_t_ss[tid] == t;
    assume ideasInv(og_global_old_put_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_H, 
      og_global_old_T, 
      og_global_old_take_in_cs, 
      og_global_old_steal_in_cs, 
      og_global_old_h_ss, 
      og_global_old_t_ss);
    assume t == og_global_old_T && task == og_global_old_items[og_global_old_T];
    assume og_global_old_T > og_global_old_H
       ==> og_global_old_items[og_global_old_T] != EMPTY;
    assume oldH <= og_global_old_H
       && oldT == og_global_old_T
       && !og_global_old_put_in_cs
       && og_global_old_take_in_cs;
    assert H >= h;
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T)
       && tid == ptTid
       && take_in_cs
       && h_ss[tid] == h
       && t_ss[tid] == t;
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert t == T && task == items[T];
    assert T > H ==> items[T] != EMPTY;
    assert oldH <= H && oldT == T && !put_in_cs && take_in_cs;
    assume false;
    return;

  L6:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume queueInv(og_global_old_steal_in_cs, 
        og_global_old_put_in_cs, 
        og_global_old_take_in_cs, 
        og_global_old_items, 
        og_global_old_status, 
        og_global_old_H, 
        og_global_old_T - 1)
       && tid == ptTid
       && og_global_old_h_ss[tid] == h
       && og_global_old_t_ss[tid] == t;
    assume ideasInv(og_global_old_put_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_H, 
      og_global_old_T, 
      og_global_old_take_in_cs, 
      og_global_old_steal_in_cs, 
      og_global_old_h_ss, 
      og_global_old_t_ss);
    assume og_global_old_T == h + 1;
    assume oldH <= og_global_old_H;
    assume oldT == og_global_old_T;
    assume task == og_global_old_items[t];
    assume !og_global_old_put_in_cs;
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && h_ss[tid] == h
       && t_ss[tid] == t;
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert T == h + 1;
    assert oldH <= H;
    assert oldT == T;
    assert task == items[t];
    assert !put_in_cs;
    assume false;
    return;

  L7:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume chk ==> h + 1 == oldH && og_global_old_h_ss[tid] == oldH - 1 && task != EMPTY;
    assume queueInv(og_global_old_steal_in_cs, 
        og_global_old_put_in_cs, 
        og_global_old_take_in_cs, 
        og_global_old_items, 
        og_global_old_status, 
        og_global_old_H, 
        og_global_old_T - 1)
       && tid == ptTid
       && og_global_old_h_ss[tid] == h
       && og_global_old_t_ss[tid] == t;
    assume ideasInv(og_global_old_put_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_H, 
      og_global_old_T, 
      og_global_old_take_in_cs, 
      og_global_old_steal_in_cs, 
      og_global_old_h_ss, 
      og_global_old_t_ss);
    assume h + 1 == og_global_old_T;
    assume task == og_global_old_items[t];
    assume !og_global_old_take_in_cs;
    assume !og_global_old_put_in_cs;
    assume oldH <= og_global_old_H && oldT == og_global_old_T;
    assert chk ==> h + 1 == oldH && h_ss[tid] == oldH - 1 && task != EMPTY;
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && h_ss[tid] == h
       && t_ss[tid] == t;
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert h + 1 == T;
    assert task == items[t];
    assert !take_in_cs;
    assert !put_in_cs;
    assert oldH <= H && oldT == T;
    assume false;
    return;

  L8:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume queueInv(og_global_old_steal_in_cs, 
        og_global_old_put_in_cs, 
        og_global_old_take_in_cs, 
        og_global_old_items, 
        og_global_old_status, 
        og_global_old_H, 
        og_global_old_T - 1)
       && tid == ptTid
       && og_global_old_h_ss[tid] == h
       && og_global_old_t_ss[tid] == t;
    assume ideasInv(og_global_old_put_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_H, 
      og_global_old_T, 
      og_global_old_take_in_cs, 
      og_global_old_steal_in_cs, 
      og_global_old_h_ss, 
      og_global_old_t_ss);
    assume h + 1 == og_global_old_T
       && task == og_global_old_items[t]
       && !og_global_old_take_in_cs
       && !og_global_old_put_in_cs;
    assume oldH <= og_global_old_H && oldT == og_global_old_T;
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && h_ss[tid] == h
       && t_ss[tid] == t;
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert h + 1 == T && task == items[t] && !take_in_cs && !put_in_cs;
    assert oldH <= H && oldT == T;
    assume false;
    return;

  L9:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume queueInv(og_global_old_steal_in_cs, 
        og_global_old_put_in_cs, 
        og_global_old_take_in_cs, 
        og_global_old_items, 
        og_global_old_status, 
        og_global_old_H, 
        og_global_old_T - 1)
       && tid == ptTid
       && og_global_old_h_ss[tid] == h
       && og_global_old_t_ss[tid] == t;
    assume ideasInv(og_global_old_put_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_H, 
      og_global_old_T, 
      og_global_old_take_in_cs, 
      og_global_old_steal_in_cs, 
      og_global_old_h_ss, 
      og_global_old_t_ss);
    assume h + 1 == og_global_old_T
       && task == og_global_old_items[t]
       && !og_global_old_take_in_cs
       && !og_global_old_put_in_cs;
    assume oldH <= og_global_old_H
       && oldT == og_global_old_T
       && task != EMPTY
       && (taskstatus <==> IN_Q);
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && h_ss[tid] == h
       && t_ss[tid] == t;
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert h + 1 == T && task == items[t] && !take_in_cs && !put_in_cs;
    assert oldH <= H && oldT == T && task != EMPTY && (taskstatus <==> IN_Q);
    assume false;
    return;

  L10:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume queueInv(og_global_old_steal_in_cs, 
        og_global_old_put_in_cs, 
        og_global_old_take_in_cs, 
        og_global_old_items, 
        og_global_old_status, 
        og_global_old_H, 
        og_global_old_T - 1)
       && tid == ptTid
       && !og_global_old_take_in_cs
       && og_global_old_h_ss[tid] == h
       && og_global_old_t_ss[tid] == t;
    assume ideasInv(og_global_old_put_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_H, 
      og_global_old_T, 
      og_global_old_take_in_cs, 
      og_global_old_steal_in_cs, 
      og_global_old_h_ss, 
      og_global_old_t_ss);
    assume t == og_global_old_T
       && task == og_global_old_items[t]
       && task != EMPTY
       && (taskstatus <==> IN_Q);
    assume oldH <= og_global_old_H
       && oldT == og_global_old_T
       && !og_global_old_put_in_cs
       && !og_global_old_take_in_cs;
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && !take_in_cs
       && h_ss[tid] == h
       && t_ss[tid] == t;
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert t == T && task == items[t] && task != EMPTY && (taskstatus <==> IN_Q);
    assert oldH <= H && oldT == T && !put_in_cs && !take_in_cs;
    assume false;
    return;

  L11:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume h <= og_global_old_H;
    assume queueInv(og_global_old_steal_in_cs, 
        og_global_old_put_in_cs, 
        og_global_old_take_in_cs, 
        og_global_old_items, 
        og_global_old_status, 
        og_global_old_H, 
        og_global_old_T - 1)
       && tid == ptTid
       && !og_global_old_take_in_cs
       && !og_global_old_put_in_cs;
    assume ideasInv(og_global_old_put_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_H, 
      og_global_old_T, 
      og_global_old_take_in_cs, 
      og_global_old_steal_in_cs, 
      og_global_old_h_ss, 
      og_global_old_t_ss);
    assume h == og_global_old_T;
    assume oldH <= og_global_old_H && oldT == og_global_old_T;
    assert h <= H;
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1)
       && tid == ptTid
       && !take_in_cs
       && !put_in_cs;
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert h == T;
    assert oldH <= H && oldT == T;
    assume false;
    return;

  L12:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume queueInv(og_global_old_steal_in_cs, 
        og_global_old_put_in_cs, 
        og_global_old_take_in_cs, 
        og_global_old_items, 
        og_global_old_status, 
        og_global_old_H, 
        og_global_old_T)
       && tid == ptTid
       && !og_global_old_put_in_cs;
    assume ideasInv(og_global_old_put_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_H, 
      og_global_old_T, 
      og_global_old_take_in_cs, 
      og_global_old_steal_in_cs, 
      og_global_old_h_ss, 
      og_global_old_t_ss);
    assume oldH <= og_global_old_H && oldT == og_global_old_T;
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T)
       && tid == ptTid
       && !put_in_cs;
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert oldH <= H && oldT == T;
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_steal_3(linear_tid_in: [Tid]bool, 
    og_global_old_H: int, 
    og_global_old_T: int, 
    og_global_old_items: [int]int, 
    og_global_old_status: [int]bool, 
    og_global_old_take_in_cs: bool, 
    og_global_old_put_in_cs: bool, 
    og_global_old_steal_in_cs: [Tid]bool, 
    og_global_old_h_ss: [Tid]int, 
    og_global_old_t_ss: [Tid]int, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var h: int;
  var t: int;
  var chk: bool;
  var oldH: int;
  var oldT: int;
  var tid: Tid;
  var task: int;
  var taskstatus: bool;
  var og_local_old_H: int;
  var og_local_old_T: int;
  var og_local_old_items: [int]int;
  var og_local_old_status: [int]bool;
  var og_local_old_take_in_cs: bool;
  var og_local_old_put_in_cs: bool;
  var og_local_old_steal_in_cs: [Tid]bool;
  var og_local_old_h_ss: [Tid]int;
  var og_local_old_t_ss: [Tid]int;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0, L1, L2, L3, L4, L5, L6, L7, L8;

  exit:
    return;

  L0:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume stealerTid(tid);
    assume queueInv(og_global_old_steal_in_cs, 
      og_global_old_put_in_cs, 
      og_global_old_take_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_H, 
      og_global_old_T - 1);
    assume ideasInv(og_global_old_put_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_H, 
      og_global_old_T, 
      og_global_old_take_in_cs, 
      og_global_old_steal_in_cs, 
      og_global_old_h_ss, 
      og_global_old_t_ss);
    assume oldH <= og_global_old_H;
    assume !og_global_old_steal_in_cs[tid];
    assert stealerTid(tid);
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert oldH <= H;
    assert !steal_in_cs[tid];
    assume false;
    return;

  L1:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume stealerTid(tid);
    assume queueInv(og_global_old_steal_in_cs, 
      og_global_old_put_in_cs, 
      og_global_old_take_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_H, 
      og_global_old_T - 1);
    assume ideasInv(og_global_old_put_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_H, 
      og_global_old_T, 
      og_global_old_take_in_cs, 
      og_global_old_steal_in_cs, 
      og_global_old_h_ss, 
      og_global_old_t_ss);
    assume oldH <= og_global_old_H;
    assume !og_global_old_steal_in_cs[tid];
    assert stealerTid(tid);
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert oldH <= H;
    assert !steal_in_cs[tid];
    assume false;
    return;

  L2:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume og_global_old_H >= h;
    assume !og_global_old_steal_in_cs[tid];
    assume og_global_old_h_ss[tid] == h;
    assume queueInv(og_global_old_steal_in_cs, 
      og_global_old_put_in_cs, 
      og_global_old_take_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_H, 
      og_global_old_T - 1);
    assume ideasInv(og_global_old_put_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_H, 
      og_global_old_T, 
      og_global_old_take_in_cs, 
      og_global_old_steal_in_cs, 
      og_global_old_h_ss, 
      og_global_old_t_ss);
    assume oldH <= og_global_old_H;
    assert H >= h;
    assert !steal_in_cs[tid];
    assert h_ss[tid] == h;
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
    assert {:expand} ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert oldH <= H;
    assume false;
    return;

  L3:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume og_global_old_steal_in_cs[tid];
    assume stealerTid(tid)
       && og_global_old_H >= h
       && og_global_old_steal_in_cs[tid]
       && og_global_old_h_ss[tid] == h;
    assume queueInv(og_global_old_steal_in_cs, 
      og_global_old_put_in_cs, 
      og_global_old_take_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_H, 
      og_global_old_T - 1);
    assume ideasInv(og_global_old_put_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_H, 
      og_global_old_T, 
      og_global_old_take_in_cs, 
      og_global_old_steal_in_cs, 
      og_global_old_h_ss, 
      og_global_old_t_ss);
    assume oldH <= og_global_old_H && t == og_global_old_t_ss[tid];
    assume h < t
         && og_global_old_take_in_cs
         && og_global_old_h_ss[ptTid] < og_global_old_t_ss[ptTid]
         && h == og_global_old_H
       ==> og_global_old_H < og_global_old_T;
    assume og_global_old_H >= h;
    assert steal_in_cs[tid];
    assert stealerTid(tid) && H >= h && steal_in_cs[tid] && h_ss[tid] == h;
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert oldH <= H && t == t_ss[tid];
    assert h < t && take_in_cs && h_ss[ptTid] < t_ss[ptTid] && h == H ==> H < T;
    assert H >= h;
    assume false;
    return;

  L4:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume stealerTid(tid)
       && og_global_old_steal_in_cs[tid]
       && og_global_old_h_ss[tid] == h;
    assume queueInv(og_global_old_steal_in_cs, 
      og_global_old_put_in_cs, 
      og_global_old_take_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_H, 
      og_global_old_T - 1);
    assume ideasInv(og_global_old_put_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_H, 
      og_global_old_T, 
      og_global_old_take_in_cs, 
      og_global_old_steal_in_cs, 
      og_global_old_h_ss, 
      og_global_old_t_ss);
    assume oldH <= og_global_old_H;
    assume oldH == og_global_old_H && og_global_old_H == h && og_global_old_h_ss[tid] == h
       ==> task != EMPTY;
    assume og_global_old_take_in_cs
         && og_global_old_h_ss[ptTid] < og_global_old_t_ss[ptTid]
         && h == og_global_old_H
       ==> og_global_old_H < og_global_old_T;
    assume h == og_global_old_H ==> (og_global_old_status[og_global_old_H] <==> IN_Q);
    assert stealerTid(tid) && steal_in_cs[tid] && h_ss[tid] == h;
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert oldH <= H;
    assert oldH == H && H == h && h_ss[tid] == h ==> task != EMPTY;
    assert take_in_cs && h_ss[ptTid] < t_ss[ptTid] && h == H ==> H < T;
    assert h == H ==> (status[H] <==> IN_Q);
    assume false;
    return;

  L5:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume og_global_old_h_ss[tid] == h;
    assume chk
       ==> h + 1 == oldH
         && og_global_old_h_ss[tid] == h
         && task != EMPTY
         && (taskstatus <==> IN_Q);
    assume og_global_old_take_in_cs
         && og_global_old_h_ss[ptTid] < og_global_old_t_ss[ptTid]
         && chk
       ==> oldH - 1 < og_global_old_T;
    assume ideasInv(og_global_old_put_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_H, 
      og_global_old_T, 
      og_global_old_take_in_cs, 
      og_global_old_steal_in_cs, 
      og_global_old_h_ss, 
      og_global_old_t_ss);
    assume stealerTid(tid) && !og_global_old_steal_in_cs[tid];
    assume queueInv(og_global_old_steal_in_cs, 
      og_global_old_put_in_cs, 
      og_global_old_take_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_H, 
      og_global_old_T - 1);
    assume oldH <= og_global_old_H;
    assert h_ss[tid] == h;
    assert chk
       ==> h + 1 == oldH && h_ss[tid] == h && task != EMPTY && (taskstatus <==> IN_Q);
    assert take_in_cs && h_ss[ptTid] < t_ss[ptTid] && chk ==> oldH - 1 < T;
    assert {:expand} ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert stealerTid(tid) && !steal_in_cs[tid];
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
    assert oldH <= H;
    assume false;
    return;

  L6:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume stealerTid(tid) && !og_global_old_steal_in_cs[tid];
    assume queueInv(og_global_old_steal_in_cs, 
      og_global_old_put_in_cs, 
      og_global_old_take_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_H, 
      og_global_old_T - 1);
    assume ideasInv(og_global_old_put_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_H, 
      og_global_old_T, 
      og_global_old_take_in_cs, 
      og_global_old_steal_in_cs, 
      og_global_old_h_ss, 
      og_global_old_t_ss);
    assume oldH <= og_global_old_H && task != EMPTY;
    assert stealerTid(tid) && !steal_in_cs[tid];
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert oldH <= H && task != EMPTY;
    assume false;
    return;

  L7:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume !og_global_old_steal_in_cs[tid];
    assume stealerTid(tid)
       && !og_global_old_steal_in_cs[tid]
       && og_global_old_h_ss[tid] == h;
    assume queueInv(og_global_old_steal_in_cs, 
      og_global_old_put_in_cs, 
      og_global_old_take_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_H, 
      og_global_old_T - 1);
    assume ideasInv(og_global_old_put_in_cs, 
      og_global_old_items, 
      og_global_old_status, 
      og_global_old_H, 
      og_global_old_T, 
      og_global_old_take_in_cs, 
      og_global_old_steal_in_cs, 
      og_global_old_h_ss, 
      og_global_old_t_ss);
    assume oldH <= og_global_old_H;
    assert !steal_in_cs[tid];
    assert stealerTid(tid) && !steal_in_cs[tid] && h_ss[tid] == h;
    assert queueInv(steal_in_cs, put_in_cs, take_in_cs, items, status, H, T - 1);
    assert ideasInv(put_in_cs, items, status, H, T, take_in_cs, steal_in_cs, h_ss, t_ss);
    assert oldH <= H;
    assume false;
    return;

  L8:
    assume (exists partition_tid: [Tid]int :: 
      linear_tid_MapImp(linear_tid_in, linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(0)))
           == linear_tid_MapConstBool(true)
         && linear_tid_MapImp(TidCollector(tid), linear_tid_MapEq(partition_tid, linear_tid_MapConstInt(1)))
           == linear_tid_MapConstBool(true));
    assume chk && task != EMPTY;
    assume stealerTid(tid) && !og_global_old_steal_in_cs[tid];
    assume oldH <= og_global_old_H;
    assert chk && task != EMPTY;
    assert stealerTid(tid) && !steal_in_cs[tid];
    assert oldH <= H;
    assume false;
    return;
}



procedure {:inline 1} og_yield_3(linear_tid_in: [Tid]bool, 
    og_global_old_H: int, 
    og_global_old_T: int, 
    og_global_old_items: [int]int, 
    og_global_old_status: [int]bool, 
    og_global_old_take_in_cs: bool, 
    og_global_old_put_in_cs: bool, 
    og_global_old_steal_in_cs: [Tid]bool, 
    og_global_old_h_ss: [Tid]int, 
    og_global_old_t_ss: [Tid]int, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



implementation {:inline 1} og_yield_3(linear_tid_in: [Tid]bool, 
    og_global_old_H: int, 
    og_global_old_T: int, 
    og_global_old_items: [int]int, 
    og_global_old_status: [int]bool, 
    og_global_old_take_in_cs: bool, 
    og_global_old_put_in_cs: bool, 
    og_global_old_steal_in_cs: [Tid]bool, 
    og_global_old_h_ss: [Tid]int, 
    og_global_old_t_ss: [Tid]int, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{

  enter:
    goto L_0, L_1, L_2;

  L_0:
    call Impl_YieldChecker_put_3(linear_tid_in, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset);
    return;

  L_1:
    call Impl_YieldChecker_take_3(linear_tid_in, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset);
    return;

  L_2:
    call Impl_YieldChecker_steal_3(linear_tid_in, og_global_old_H, og_global_old_T, og_global_old_items, og_global_old_status, og_global_old_take_in_cs, og_global_old_put_in_cs, og_global_old_steal_in_cs, og_global_old_h_ss, og_global_old_t_ss, og_global_old_pendingAsyncMultiset);
    return;
}


