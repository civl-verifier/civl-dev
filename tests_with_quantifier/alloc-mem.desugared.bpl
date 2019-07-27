// Boogie program verifier version 2.4.1.10503, Copyright (c) 2003-2014, Microsoft.
// Command Line Options: /noWitnessInference /noCommutativityTriggers /noVerify /CivlDesugaredFile:desugared_files/alloc-mem.desugared.bpl ../alloc-mem.bpl

function {:builtin "MapConst"} MapConstBool(bool) : [int]bool;

type lmap;

function dom(lmap) : [int]bool;

function map(lmap) : [int]int;

function cons([int]bool, [int]int) : lmap;

axiom (forall x: [int]bool, y: [int]int :: 
  { cons(x, y) } 
  dom(cons(x, y)) == x && map(cons(x, y)) == y);

axiom (forall x: lmap :: { dom(x) } { map(x) } cons(dom(x), map(x)) == x);

function Empty(m: [int]int) : lmap;

axiom (forall m: [int]int :: Empty(m) == cons(MapConstBool(false), m));

function Add(x: lmap, i: int) : lmap;

axiom (forall x: lmap, i: int :: 
  dom(Add(x, i)) == dom(x)[i := true] && map(Add(x, i)) == map(x));

function Remove(x: lmap, i: int) : lmap;

axiom (forall x: lmap, i: int :: 
  dom(Remove(x, i)) == dom(x)[i := false] && map(Remove(x, i)) == map(x));

function {:inline} PoolInv(unallocated: [int]bool, pool: lmap) : bool
{
  (forall x: int :: unallocated[x] ==> dom(pool)[x])
}

procedure AllocLinear(i: int) returns (l: lmap);
  requires dom(pool)[i];
  modifies pool;
  ensures pool == Remove(old(pool), i) && l == Add(Empty(mem), i);
  free ensures (exists partition_mem: [int]int :: 
    linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
         == linear_mem_MapConstBool(true)
       && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
         == linear_mem_MapConstBool(true));



procedure FreeLinear(l: lmap, i: int);
  requires dom(l)[i];
  free requires (exists partition_mem: [int]int :: 
    linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
         == linear_mem_MapConstBool(true)
       && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
         == linear_mem_MapConstBool(true));
  modifies pool;
  ensures pool == Add(old(pool), i);



procedure WriteLinear(l: lmap, i: int, o: int) returns (l': lmap);
  requires dom(l)[i];
  free requires (exists partition_mem: [int]int :: 
    linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
         == linear_mem_MapConstBool(true)
       && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
         == linear_mem_MapConstBool(true));
  ensures l' == cons(dom(l), map(l)[i := o]);
  free ensures (exists partition_mem: [int]int :: 
    linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
         == linear_mem_MapConstBool(true)
       && linear_mem_MapImp(dom(l'), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
         == linear_mem_MapConstBool(true));



var pool: lmap;

var mem: [int]int;

var unallocated: [int]bool;

type {:datatype} PendingAsync;

var pendingAsyncMultiset: [PendingAsync]int;

function {:constructor} PendingAsync_Alloc() : PendingAsync;

procedure {:inline 1} AddPendingAsync_Alloc();
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_Alloc()
{

  L:
    pendingAsyncMultiset[PendingAsync_Alloc()] := pendingAsyncMultiset[PendingAsync_Alloc()] + 1;
    return;
}



function {:constructor} PendingAsync_Free(l: lmap, i: int) : PendingAsync;

procedure {:inline 1} AddPendingAsync_Free(l: lmap, i: int);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_Free(l: lmap, i: int)
{

  L:
    pendingAsyncMultiset[PendingAsync_Free(l, i)] := pendingAsyncMultiset[PendingAsync_Free(l, i)] + 1;
    return;
}



function {:constructor} PendingAsync_Read(l: lmap, i: int) : PendingAsync;

procedure {:inline 1} AddPendingAsync_Read(l: lmap, i: int);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_Read(l: lmap, i: int)
{

  L:
    pendingAsyncMultiset[PendingAsync_Read(l, i)] := pendingAsyncMultiset[PendingAsync_Read(l, i)] + 1;
    return;
}



function {:constructor} PendingAsync_Write(l: lmap, i: int, o: int) : PendingAsync;

procedure {:inline 1} AddPendingAsync_Write(l: lmap, i: int, o: int);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_Write(l: lmap, i: int, o: int)
{

  L:
    pendingAsyncMultiset[PendingAsync_Write(l, i, o)] := pendingAsyncMultiset[PendingAsync_Write(l, i, o)] + 1;
    return;
}



function {:constructor} PendingAsync_ReadLow(i: int) : PendingAsync;

procedure {:inline 1} AddPendingAsync_ReadLow(i: int);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_ReadLow(i: int)
{

  L:
    pendingAsyncMultiset[PendingAsync_ReadLow(i)] := pendingAsyncMultiset[PendingAsync_ReadLow(i)] + 1;
    return;
}



function {:constructor} PendingAsync_WriteLow(i: int, o: int) : PendingAsync;

procedure {:inline 1} AddPendingAsync_WriteLow(i: int, o: int);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_WriteLow(i: int, o: int)
{

  L:
    pendingAsyncMultiset[PendingAsync_WriteLow(i, o)] := pendingAsyncMultiset[PendingAsync_WriteLow(i, o)] + 1;
    return;
}



function {:constructor} PendingAsync_PickAddr() : PendingAsync;

procedure {:inline 1} AddPendingAsync_PickAddr();
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_PickAddr()
{

  L:
    pendingAsyncMultiset[PendingAsync_PickAddr()] := pendingAsyncMultiset[PendingAsync_PickAddr()] + 1;
    return;
}



function {:constructor} PendingAsync_ReturnAddr(i: int) : PendingAsync;

procedure {:inline 1} AddPendingAsync_ReturnAddr(i: int);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_ReturnAddr(i: int)
{

  L:
    pendingAsyncMultiset[PendingAsync_ReturnAddr(i)] := pendingAsyncMultiset[PendingAsync_ReturnAddr(i)] + 1;
    return;
}



procedure {:inline 1} atomic_ReadLow_1(i: int) returns (o: int);



procedure {:inline 1} atomic_WriteLow_1(i: int, o: int);
  modifies mem;



procedure {:inline 1} atomic_PickAddr_1() returns (i: int);
  modifies unallocated;



procedure {:inline 1} atomic_ReturnAddr_1(i: int);
  modifies unallocated;



implementation {:inline 1} atomic_ReadLow_1(i: int) returns (o: int)
{
  /*** structured program:
    o := mem[i];
  **** end structured program */

  anon0:
    o := mem[i];
    return;
}



implementation {:inline 1} atomic_WriteLow_1(i: int, o: int)
{
  /*** structured program:
    mem[i] := o;
  **** end structured program */

  anon0:
    mem[i] := o;
    return;
}



implementation {:inline 1} atomic_PickAddr_1() returns (i: int)
{
  /*** structured program:
    assume unallocated[i];
    unallocated[i] := false;
  **** end structured program */

  anon0:
    assume unallocated[i];
    unallocated[i] := false;
    return;
}



implementation {:inline 1} atomic_ReturnAddr_1(i: int)
{
  /*** structured program:
    unallocated[i] := true;
  **** end structured program */

  anon0:
    unallocated[i] := true;
    return;
}



procedure {:inline 1} atomic_Alloc_2() returns (l: lmap, i: int);
  modifies pool;
  free ensures (exists partition_mem: [int]int :: 
    linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
         == linear_mem_MapConstBool(true)
       && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
         == linear_mem_MapConstBool(true));



procedure {:inline 1} atomic_Free_2(l: lmap, i: int);
  free requires (exists partition_mem: [int]int :: 
    linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
         == linear_mem_MapConstBool(true)
       && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
         == linear_mem_MapConstBool(true));
  modifies pool;



procedure {:inline 1} atomic_Read_2(l: lmap, i: int) returns (o: int);
  free requires (exists partition_mem: [int]int :: 
    linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
         == linear_mem_MapConstBool(true)
       && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
         == linear_mem_MapConstBool(true));



procedure {:inline 1} atomic_Write_2(l: lmap, i: int, o: int) returns (l': lmap);
  free requires (exists partition_mem: [int]int :: 
    linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
         == linear_mem_MapConstBool(true)
       && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
         == linear_mem_MapConstBool(true));
  free ensures (exists partition_mem: [int]int :: 
    linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
         == linear_mem_MapConstBool(true)
       && linear_mem_MapImp(dom(l'), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
         == linear_mem_MapConstBool(true));



implementation {:inline 1} atomic_Alloc_2() returns (l: lmap, i: int)
{
  var m: [int]int;

  /*** structured program:
    assume dom(pool)[i];
    pool := Remove(pool, i);
    l := Add(Empty(m), i);
  **** end structured program */

  anon0:
    assume dom(pool)[i];
    pool := Remove(pool, i);
    l := Add(Empty(m), i);
    return;
}



implementation {:inline 1} atomic_Free_2(l: lmap, i: int)
{
  /*** structured program:
    assert dom(l)[i];
    pool := Add(pool, i);
  **** end structured program */

  anon0:
    pool := Add(pool, i);
    return;
}



implementation {:inline 1} atomic_Read_2(l: lmap, i: int) returns (o: int)
{
  /*** structured program:
    assert dom(l)[i];
    o := map(l)[i];
  **** end structured program */

  anon0:
    o := map(l)[i];
    return;
}



implementation {:inline 1} atomic_Write_2(l: lmap, i: int, o: int) returns (l': lmap)
{
  /*** structured program:
    assert dom(l)[i];
    l' := cons(dom(l), map(l)[i := o]);
  **** end structured program */

  anon0:
    l' := cons(dom(l), map(l)[i := o]);
    return;
}



var linear_mem_hole: [int]bool;

function linear_mem_MapConstBool(b: bool) : [int]bool;

function linear_mem_MapConstInt(b: int) : [int]int;

function linear_mem_MapEq(a: [int]int, b: [int]int) : [int]bool;

function linear_mem_MapImp(a: [int]bool, b: [int]bool) : [int]bool;

function linear_mem_MapOr(a: [int]bool, b: [int]bool) : [int]bool;

axiom (forall a: [int]bool, b: [int]bool :: 
  { linear_mem_MapOr(a, b) } 
  (forall x: int :: linear_mem_MapOr(a, b)[x] <==> a[x] || b[x]));

axiom (forall a: [int]bool, b: [int]bool :: 
  { linear_mem_MapImp(a, b) } 
  (forall x: int :: linear_mem_MapImp(a, b)[x] <==> a[x] ==> b[x]));

axiom (forall x: int :: linear_mem_MapConstBool(true)[x]);

axiom (forall x: int :: !linear_mem_MapConstBool(false)[x]);

axiom (forall a: [int]int, b: [int]int :: 
  { linear_mem_MapEq(a, b) } 
  (forall x: int :: linear_mem_MapEq(a, b)[x] <==> a[x] == b[x]));

axiom (forall a: int, x: int :: linear_mem_MapConstInt(a)[x] == a);

implementation CommutativityChecker_atomic_Alloc_2_atomic_Alloc_2() returns (first_l: lmap, first_i: int, second_l: lmap, second_i: int)
{
  var first_m: [int]int;
  var second_m: [int]int;

  first_anon0:
    assume dom(pool)[first_i];
    pool := Remove(pool, first_i);
    first_l := Add(Empty(first_m), first_i);
    goto second_anon0;

  second_anon0:
    assume dom(pool)[second_i];
    pool := Remove(pool, second_i);
    second_l := Add(Empty(second_m), second_i);
    return;
}



procedure CommutativityChecker_atomic_Alloc_2_atomic_Alloc_2() returns (first_l: lmap, first_i: int, second_l: lmap, second_i: int);
  requires true;
  modifies pool, mem, unallocated, pendingAsyncMultiset;
  ensures (exists partition_mem: [int]int :: 
        linear_mem_MapImp(dom(first_l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
             == linear_mem_MapConstBool(true)
           && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
             == linear_mem_MapConstBool(true))
       && (exists partition_mem: [int]int :: 
        linear_mem_MapImp(dom(first_l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
             == linear_mem_MapConstBool(true)
           && linear_mem_MapImp(dom(second_l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
             == linear_mem_MapConstBool(true)
           && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
             == linear_mem_MapConstBool(true))
     ==> (exists #tmp_0_first_m: [int]int, #tmp_1_second_m: [int]int :: 
      pool == Remove(Remove(old(pool), second_i), first_i)
         && first_l == Add(Empty(#tmp_0_first_m), first_i)
         && first_i == first_i
         && second_l == Add(Empty(#tmp_1_second_m), second_i)
         && second_i == second_i
         && dom(Remove(old(pool), second_i))[first_i]
         && dom(old(pool))[second_i]);



implementation CommutativityChecker_atomic_Alloc_2_atomic_Free_2(second_l: lmap, second_i: int) returns (first_l: lmap, first_i: int)
{
  var first_m: [int]int;

  first_anon0:
    assume dom(pool)[first_i];
    pool := Remove(pool, first_i);
    first_l := Add(Empty(first_m), first_i);
    goto second_anon0;

  second_anon0:
    pool := Add(pool, second_i);
    return;
}



procedure CommutativityChecker_atomic_Alloc_2_atomic_Free_2(second_l: lmap, second_i: int) returns (first_l: lmap, first_i: int);
  requires (exists partition_mem: [int]int :: 
    linear_mem_MapImp(dom(second_l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
         == linear_mem_MapConstBool(true)
       && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
         == linear_mem_MapConstBool(true));
  requires dom(second_l)[second_i];
  modifies pool, mem, unallocated, pendingAsyncMultiset;
  ensures (exists partition_mem: [int]int :: 
        linear_mem_MapImp(dom(first_l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
             == linear_mem_MapConstBool(true)
           && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
             == linear_mem_MapConstBool(true))
       && (exists partition_mem: [int]int :: 
        linear_mem_MapImp(dom(first_l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
             == linear_mem_MapConstBool(true)
           && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
             == linear_mem_MapConstBool(true))
     ==> (exists #tmp_0_first_m: [int]int :: 
      pool == Remove(Add(old(pool), second_i), first_i)
         && first_l == Add(Empty(#tmp_0_first_m), first_i)
         && first_i == first_i
         && dom(Add(old(pool), second_i))[first_i]);



implementation CommutativityChecker_atomic_Free_2_atomic_Free_2(first_l: lmap, first_i: int, second_l: lmap, second_i: int)
{

  first_anon0:
    pool := Add(pool, first_i);
    goto second_anon0;

  second_anon0:
    pool := Add(pool, second_i);
    return;
}



procedure CommutativityChecker_atomic_Free_2_atomic_Free_2(first_l: lmap, first_i: int, second_l: lmap, second_i: int);
  requires (exists partition_mem: [int]int :: 
    linear_mem_MapImp(dom(first_l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
         == linear_mem_MapConstBool(true)
       && linear_mem_MapImp(dom(second_l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
         == linear_mem_MapConstBool(true)
       && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
         == linear_mem_MapConstBool(true));
  requires dom(first_l)[first_i];
  requires dom(second_l)[second_i];
  modifies pool, mem, unallocated, pendingAsyncMultiset;
  ensures true ==> pool == Add(Add(old(pool), second_i), first_i);



procedure {:inline 1} skip_dummy_Main();



implementation {:inline 1} skip_dummy_Main()
{

  _init:
    return;
}



procedure {:inline 1} skip_dummy_Thread(local_in: lmap, i: int);



implementation {:inline 1} skip_dummy_Thread(local_in: lmap, i: int)
{

  _init:
    return;
}



procedure {:inline 1} skip_dummy_Yield();



implementation {:inline 1} skip_dummy_Yield()
{

  _init:
    return;
}



procedure {:inline 1} skip_dummy_YieldMem(l: lmap, i: int);



implementation {:inline 1} skip_dummy_YieldMem(l: lmap, i: int)
{

  _init:
    return;
}



procedure {:inline 1} skip_dummy_Dummy();



implementation {:inline 1} skip_dummy_Dummy()
{

  _init:
    return;
}



procedure Main_0();
  modifies pool, mem, unallocated, pendingAsyncMultiset;



procedure Thread_0(local_in: lmap, i: int);
  free requires (exists partition_mem: [int]int :: 
    linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
         == linear_mem_MapConstBool(true)
       && linear_mem_MapImp(dom(local_in), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
         == linear_mem_MapConstBool(true));
  modifies pool, mem, unallocated, pendingAsyncMultiset;



procedure Alloc_0() returns (l: lmap, i: int);
  modifies pool, mem, unallocated, pendingAsyncMultiset;
  free ensures (exists partition_mem: [int]int :: 
    linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
         == linear_mem_MapConstBool(true)
       && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
         == linear_mem_MapConstBool(true));



procedure Free_0(l: lmap, i: int);
  free requires (exists partition_mem: [int]int :: 
    linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
         == linear_mem_MapConstBool(true)
       && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
         == linear_mem_MapConstBool(true));
  modifies pool, mem, unallocated, pendingAsyncMultiset;



procedure Read_0(l: lmap, i: int) returns (o: int);
  free requires (exists partition_mem: [int]int :: 
    linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
         == linear_mem_MapConstBool(true)
       && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
         == linear_mem_MapConstBool(true));
  modifies pool, mem, unallocated, pendingAsyncMultiset;



procedure Write_0(l: lmap, i: int, o: int) returns (l': lmap);
  free requires (exists partition_mem: [int]int :: 
    linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
         == linear_mem_MapConstBool(true)
       && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
         == linear_mem_MapConstBool(true));
  modifies pool, mem, unallocated, pendingAsyncMultiset;
  free ensures (exists partition_mem: [int]int :: 
    linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
         == linear_mem_MapConstBool(true)
       && linear_mem_MapImp(dom(l'), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
         == linear_mem_MapConstBool(true));



procedure Yield_0();
  modifies pool, mem, unallocated, pendingAsyncMultiset;



procedure YieldMem_0(l: lmap, i: int);
  free requires (exists partition_mem: [int]int :: 
    linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
         == linear_mem_MapConstBool(true)
       && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
         == linear_mem_MapConstBool(true));
  modifies pool, mem, unallocated, pendingAsyncMultiset;



procedure Dummy_0();
  modifies pool, mem, unallocated, pendingAsyncMultiset;



procedure ReadLow_0(i: int) returns (o: int);
  modifies pool, mem, unallocated, pendingAsyncMultiset;



procedure WriteLow_0(i: int, o: int);
  modifies pool, mem, unallocated, pendingAsyncMultiset;



procedure PickAddr_0() returns (i: int);
  modifies pool, mem, unallocated, pendingAsyncMultiset;



procedure ReturnAddr_0(i: int);
  modifies pool, mem, unallocated, pendingAsyncMultiset;



implementation Main_0()
{
  var l: lmap;
  var i: int;
  var og_global_old_pool: lmap;
  var og_global_old_mem: [int]int;
  var og_global_old_unallocated: [int]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_mem_available: [int]bool;

  /*** structured program:
    while (*)
      invariant PoolInv(unallocated, pool);
    {
        call l, i := Alloc();
        async call Thread(l, i);
    }

  **** end structured program */

  og_init:
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon3_LoopHead:
    assume linear_mem_available == linear_mem_MapConstBool(false);
    assume pool == og_global_old_pool;
    assume mem == og_global_old_mem;
    assume unallocated == og_global_old_unallocated;
    assume pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    goto anon3_LoopDone, anon3_LoopBody;

  anon3_LoopBody:
    goto anon3_LoopBody0, CallToYieldProc;

  anon3_LoopDone:
    goto anon2;

  anon2:
    goto anon20, CallToYieldProc;

  anon04:
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    goto anon3_LoopHead;

  anon00:
    call og_Yield_0_Dummy_0();
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    goto anon04, CallToYieldProc;

  anon3_LoopBody12:
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    goto anon3_LoopHead;

  anon3_LoopBody8:
    call og_Yield_0_Dummy_0();
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    goto anon3_LoopBody12, CallToYieldProc;

  anon3_LoopBody4:
    call DummyAsyncTarget_Thread_0(l, i);
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    goto anon3_LoopBody8, CallToYieldProc;

  anon3_LoopBody0:
    call l, i := Alloc_0();
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon3_LoopBody4, CallToYieldProc;

  anon24:
    return;

  anon20:
    call og_Yield_0_Dummy_0();
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    goto anon24, CallToYieldProc;

  CallToYieldProc:
    call og_yield_0(linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation Thread_0(local_in: lmap, i: int)
{
  var y: int;
  var o: int;
  var local: lmap;
  var l: lmap;
  var og_global_old_pool: lmap;
  var og_global_old_mem: [int]int;
  var og_global_old_unallocated: [int]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_mem_available: [int]bool;

  /*** structured program:
    call local := Write(local_in, i, 42);
    call o := Read(local, i);
    assert o == 42;
    while (*)
      invariant PoolInv(unallocated, pool);
    {
        call l, y := Alloc();
        call l := Write(l, y, 42);
        call o := Read(l, y);
        assert o == 42;
        call Free(l, y);
    }

  **** end structured program */

  og_init:
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapOr(dom(local_in), linear_mem_MapConstBool(false)), pool, mem, unallocated, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon3_LoopHead:
    assume linear_mem_available == linear_mem_MapConstBool(false);
    assume pool == og_global_old_pool;
    assume mem == og_global_old_mem;
    assume unallocated == og_global_old_unallocated;
    assume pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(local), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon3_LoopDone, anon3_LoopBody;

  anon3_LoopBody:
    goto anon3_LoopBody0, CallToYieldProc;

  anon3_LoopDone:
    goto anon2;

  anon2:
    goto anon20, CallToYieldProc;

  anon012:
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    goto anon3_LoopHead;

  anon08:
    call o := Read_0(local, i);
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(local), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon012, CallToYieldProc;

  anon04:
    call local := Write_0(local_in, i, 42);
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(local), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon08, CallToYieldProc;

  anon00:
    call og_YieldMem_0_Dummy_0(local_in, i);
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(local_in), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon04, CallToYieldProc;

  anon3_LoopBody20:
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    goto anon3_LoopHead;

  anon3_LoopBody16:
    call og_Yield_0_Dummy_0();
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(local), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon3_LoopBody20, CallToYieldProc;

  anon3_LoopBody12:
    call Free_0(l, y);
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(local), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon3_LoopBody16, CallToYieldProc;

  anon3_LoopBody8:
    call o := Read_0(l, y);
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(local), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(3)))
           == linear_mem_MapConstBool(true));
    goto anon3_LoopBody12, CallToYieldProc;

  anon3_LoopBody4:
    call l := Write_0(l, y, 42);
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(local), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(3)))
           == linear_mem_MapConstBool(true));
    goto anon3_LoopBody8, CallToYieldProc;

  anon3_LoopBody0:
    call l, y := Alloc_0();
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(local), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(3)))
           == linear_mem_MapConstBool(true));
    goto anon3_LoopBody4, CallToYieldProc;

  anon24:
    return;

  anon20:
    call og_Yield_0_Dummy_0();
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(local), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon24, CallToYieldProc;

  CallToYieldProc:
    call og_yield_0(linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation Alloc_0() returns (l: lmap, i: int)
{
  var og_global_old_pool: lmap;
  var og_global_old_mem: [int]int;
  var og_global_old_unallocated: [int]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_mem_available: [int]bool;

  /*** structured program:
    call Yield();
    call i := PickAddr();
    call l := AllocLinear(i);
    call YieldMem(l, i);
  **** end structured program */

  og_init:
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon013:
    return;

  anon09:
    call YieldMem_0(l, i);
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon013, CallToYieldProc;

  anon04:
    call i := PickAddr_0();
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon09, CallToYieldProc;

  anon00:
    call Yield_0();
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    goto anon04, CallToYieldProc;

  CallToYieldProc:
    call og_yield_0(linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation Free_0(l: lmap, i: int)
{
  var og_global_old_pool: lmap;
  var og_global_old_mem: [int]int;
  var og_global_old_unallocated: [int]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_mem_available: [int]bool;

  /*** structured program:
    call Yield();
    call FreeLinear(l, i);
    call ReturnAddr(i);
    call Yield();
  **** end structured program */

  og_init:
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapOr(dom(l), linear_mem_MapConstBool(false)), pool, mem, unallocated, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon013:
    return;

  anon09:
    call Yield_0();
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    goto anon013, CallToYieldProc;

  anon05:
    call ReturnAddr_0(i);
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    goto anon09, CallToYieldProc;

  anon00:
    call Yield_0();
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    goto anon05, CallToYieldProc;

  CallToYieldProc:
    call og_yield_0(linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation Read_0(l: lmap, i: int) returns (o: int)
{
  var og_global_old_pool: lmap;
  var og_global_old_mem: [int]int;
  var og_global_old_unallocated: [int]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_mem_available: [int]bool;

  /*** structured program:
    call YieldMem(l, i);
    call o := ReadLow(i);
    call YieldMem(l, i);
  **** end structured program */

  og_init:
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapOr(dom(l), linear_mem_MapConstBool(false)), pool, mem, unallocated, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon012:
    return;

  anon08:
    call YieldMem_0(l, i);
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon012, CallToYieldProc;

  anon04:
    call o := ReadLow_0(i);
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon08, CallToYieldProc;

  anon00:
    call YieldMem_0(l, i);
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon04, CallToYieldProc;

  CallToYieldProc:
    call og_yield_0(linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation Write_0(l: lmap, i: int, o: int) returns (l': lmap)
{
  var og_global_old_pool: lmap;
  var og_global_old_mem: [int]int;
  var og_global_old_unallocated: [int]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_mem_available: [int]bool;

  /*** structured program:
    call YieldMem(l, i);
    call WriteLow(i, o);
    call l' := WriteLinear(l, i, o);
    call YieldMem(l', i);
  **** end structured program */

  og_init:
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapOr(dom(l), linear_mem_MapConstBool(false)), pool, mem, unallocated, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon013:
    return;

  anon09:
    call YieldMem_0(l', i);
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l'), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon013, CallToYieldProc;

  anon04:
    call WriteLow_0(i, o);
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l'), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon09, CallToYieldProc;

  anon00:
    call YieldMem_0(l, i);
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon04, CallToYieldProc;

  CallToYieldProc:
    call og_yield_0(linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation Yield_0()
{
  var og_global_old_pool: lmap;
  var og_global_old_mem: [int]int;
  var og_global_old_unallocated: [int]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_mem_available: [int]bool;

  /*** structured program:
    yield;
    assert PoolInv(unallocated, pool);
  **** end structured program */

  og_init:
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    goto anon01, CallToYieldProc;

  anon05:
    return;

  anon01:
    havoc pool, mem, unallocated, pendingAsyncMultiset;
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    goto anon05, CallToYieldProc;

  CallToYieldProc:
    call og_yield_0(linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation YieldMem_0(l: lmap, i: int)
{
  var og_global_old_pool: lmap;
  var og_global_old_mem: [int]int;
  var og_global_old_unallocated: [int]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_mem_available: [int]bool;

  /*** structured program:
    yield;
    assert PoolInv(unallocated, pool);
    assert dom(l)[i] && map(l)[i] == mem[i];
  **** end structured program */

  og_init:
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapOr(dom(l), linear_mem_MapConstBool(false)), pool, mem, unallocated, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon01, CallToYieldProc;

  anon05:
    return;

  anon01:
    havoc pool, mem, unallocated, pendingAsyncMultiset;
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon05, CallToYieldProc;

  CallToYieldProc:
    call og_yield_0(linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation Dummy_0()
{
  var og_global_old_pool: lmap;
  var og_global_old_mem: [int]int;
  var og_global_old_unallocated: [int]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_mem_available: [int]bool;

  /*** structured program:
    yield;
  **** end structured program */

  og_init:
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    goto anon01, CallToYieldProc;

  anon05:
    return;

  anon01:
    havoc pool, mem, unallocated, pendingAsyncMultiset;
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    goto anon05, CallToYieldProc;

  CallToYieldProc:
    call og_yield_0(linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



procedure {:inline 1} Impl_YieldChecker_Yield_0(linear_mem_in: [int]bool, 
    og_global_old_pool: lmap, 
    og_global_old_mem: [int]int, 
    og_global_old_unallocated: [int]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_YieldMem_0(linear_mem_in: [int]bool, 
    og_global_old_pool: lmap, 
    og_global_old_mem: [int]int, 
    og_global_old_unallocated: [int]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_Dummy_0(linear_mem_in: [int]bool, 
    og_global_old_pool: lmap, 
    og_global_old_mem: [int]int, 
    og_global_old_unallocated: [int]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



implementation {:inline 1} Impl_YieldChecker_Yield_0(linear_mem_in: [int]bool, 
    og_global_old_pool: lmap, 
    og_global_old_mem: [int]int, 
    og_global_old_unallocated: [int]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var og_local_old_pool: lmap;
  var og_local_old_mem: [int]int;
  var og_local_old_unallocated: [int]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_in, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(og_global_old_pool), 
            linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_YieldMem_0(linear_mem_in: [int]bool, 
    og_global_old_pool: lmap, 
    og_global_old_mem: [int]int, 
    og_global_old_unallocated: [int]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var l: lmap;
  var i: int;
  var og_local_old_pool: lmap;
  var og_local_old_mem: [int]int;
  var og_local_old_unallocated: [int]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_in, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(og_global_old_pool), 
            linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_Dummy_0(linear_mem_in: [int]bool, 
    og_global_old_pool: lmap, 
    og_global_old_mem: [int]int, 
    og_global_old_unallocated: [int]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var og_local_old_pool: lmap;
  var og_local_old_mem: [int]int;
  var og_local_old_unallocated: [int]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_in, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(og_global_old_pool), 
            linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    assume false;
    return;
}



procedure og_Yield_0_Dummy_0();
  modifies pool, mem, unallocated, pendingAsyncMultiset;



procedure DummyAsyncTarget_Thread_0(local_in: lmap, i: int);
  free requires (exists partition_mem: [int]int :: 
    linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
         == linear_mem_MapConstBool(true)
       && linear_mem_MapImp(dom(local_in), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
         == linear_mem_MapConstBool(true));



procedure og_YieldMem_0_Dummy_0(og_0_l: lmap, og_0_i: int);
  free requires (exists partition_mem: [int]int :: 
    linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
         == linear_mem_MapConstBool(true)
       && linear_mem_MapImp(dom(og_0_l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
         == linear_mem_MapConstBool(true));
  modifies pool, mem, unallocated, pendingAsyncMultiset;



procedure {:inline 1} og_yield_0(linear_mem_in: [int]bool, 
    og_global_old_pool: lmap, 
    og_global_old_mem: [int]int, 
    og_global_old_unallocated: [int]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



implementation {:inline 1} og_yield_0(linear_mem_in: [int]bool, 
    og_global_old_pool: lmap, 
    og_global_old_mem: [int]int, 
    og_global_old_unallocated: [int]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{

  enter:
    goto L_0, L_1, L_2;

  L_0:
    call Impl_YieldChecker_Yield_0(linear_mem_in, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset);
    return;

  L_1:
    call Impl_YieldChecker_YieldMem_0(linear_mem_in, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset);
    return;

  L_2:
    call Impl_YieldChecker_Dummy_0(linear_mem_in, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset);
    return;
}



procedure Main_1();
  requires PoolInv(unallocated, pool);
  modifies pool, mem, unallocated, pendingAsyncMultiset;
  ensures PoolInv(unallocated, pool);



procedure Thread_1(local_in: lmap, i: int);
  requires PoolInv(unallocated, pool);
  requires dom(local_in)[i] && map(local_in)[i] == mem[i];
  free requires (exists partition_mem: [int]int :: 
    linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
         == linear_mem_MapConstBool(true)
       && linear_mem_MapImp(dom(local_in), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
         == linear_mem_MapConstBool(true));
  modifies pool, mem, unallocated, pendingAsyncMultiset;
  ensures PoolInv(unallocated, pool);



procedure Alloc_1() returns (l: lmap, i: int);
  requires PoolInv(unallocated, pool);
  modifies pool, mem, unallocated, pendingAsyncMultiset;
  ensures PoolInv(unallocated, pool);
  ensures dom(l)[i] && map(l)[i] == mem[i];
  free ensures (exists partition_mem: [int]int :: 
    linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
         == linear_mem_MapConstBool(true)
       && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
         == linear_mem_MapConstBool(true));



procedure Free_1(l: lmap, i: int);
  requires PoolInv(unallocated, pool);
  requires dom(l)[i];
  free requires (exists partition_mem: [int]int :: 
    linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
         == linear_mem_MapConstBool(true)
       && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
         == linear_mem_MapConstBool(true));
  modifies pool, mem, unallocated, pendingAsyncMultiset;
  ensures PoolInv(unallocated, pool);



procedure Read_1(l: lmap, i: int) returns (o: int);
  requires PoolInv(unallocated, pool);
  requires dom(l)[i] && map(l)[i] == mem[i];
  free requires (exists partition_mem: [int]int :: 
    linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
         == linear_mem_MapConstBool(true)
       && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
         == linear_mem_MapConstBool(true));
  modifies pool, mem, unallocated, pendingAsyncMultiset;
  ensures PoolInv(unallocated, pool);



procedure Write_1(l: lmap, i: int, o: int) returns (l': lmap);
  requires PoolInv(unallocated, pool);
  requires dom(l)[i] && map(l)[i] == mem[i];
  free requires (exists partition_mem: [int]int :: 
    linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
         == linear_mem_MapConstBool(true)
       && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
         == linear_mem_MapConstBool(true));
  modifies pool, mem, unallocated, pendingAsyncMultiset;
  ensures PoolInv(unallocated, pool);
  ensures dom(l')[i] && map(l')[i] == mem[i];
  free ensures (exists partition_mem: [int]int :: 
    linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
         == linear_mem_MapConstBool(true)
       && linear_mem_MapImp(dom(l'), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
         == linear_mem_MapConstBool(true));



procedure Yield_1();
  requires PoolInv(unallocated, pool);
  modifies pool, mem, unallocated, pendingAsyncMultiset;
  ensures PoolInv(unallocated, pool);



procedure YieldMem_1(l: lmap, i: int);
  requires PoolInv(unallocated, pool);
  requires dom(l)[i] && map(l)[i] == mem[i];
  free requires (exists partition_mem: [int]int :: 
    linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
         == linear_mem_MapConstBool(true)
       && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
         == linear_mem_MapConstBool(true));
  modifies pool, mem, unallocated, pendingAsyncMultiset;
  ensures PoolInv(unallocated, pool);
  ensures dom(l)[i] && map(l)[i] == mem[i];



procedure Dummy_1();
  modifies pool, mem, unallocated, pendingAsyncMultiset;



implementation Main_1()
{
  var l: lmap;
  var i: int;
  var og_global_old_pool: lmap;
  var og_global_old_mem: [int]int;
  var og_global_old_unallocated: [int]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_mem_available: [int]bool;

  /*** structured program:
    while (*)
      invariant PoolInv(unallocated, pool);
    {
        call l, i := Alloc();
        async call Thread(l, i);
    }

  **** end structured program */

  og_init:
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon3_LoopHead:
    assume linear_mem_available == linear_mem_MapConstBool(false);
    assume pool == og_global_old_pool;
    assume mem == og_global_old_mem;
    assume unallocated == og_global_old_unallocated;
    assume pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    assert PoolInv(unallocated, pool);
    goto anon3_LoopDone, anon3_LoopBody;

  anon3_LoopBody:
    goto anon3_LoopBody0, CallToYieldProc;

  anon3_LoopDone:
    goto anon2;

  anon2:
    goto anon20, CallToYieldProc;

  anon04:
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    goto anon3_LoopHead;

  anon00:
    call og_Yield_1_Dummy_1();
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    goto anon04, CallToYieldProc;

  anon3_LoopBody12:
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    goto anon3_LoopHead;

  anon3_LoopBody8:
    call og_Yield_1_Dummy_1();
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    goto anon3_LoopBody12, CallToYieldProc;

  anon3_LoopBody4:
    call DummyAsyncTarget_Thread_1(l, i);
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    goto anon3_LoopBody8, CallToYieldProc;

  anon3_LoopBody0:
    call l, i := Alloc_1();
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapOr(dom(l), linear_mem_MapConstBool(false)), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon3_LoopBody4, CallToYieldProc;

  anon24:
    return;

  anon20:
    call og_Yield_1_Dummy_1();
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    goto anon24, CallToYieldProc;

  CallToYieldProc:
    call og_yield_1(linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation Thread_1(local_in: lmap, i: int)
{
  var y: int;
  var o: int;
  var local: lmap;
  var l: lmap;
  var og_global_old_pool: lmap;
  var og_global_old_mem: [int]int;
  var og_global_old_unallocated: [int]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_mem_available: [int]bool;

  /*** structured program:
    call local := Write(local_in, i, 42);
    call o := Read(local, i);
    assert o == 42;
    while (*)
      invariant PoolInv(unallocated, pool);
    {
        call l, y := Alloc();
        call l := Write(l, y, 42);
        call o := Read(l, y);
        assert o == 42;
        call Free(l, y);
    }

  **** end structured program */

  og_init:
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapOr(dom(local_in), linear_mem_MapConstBool(false)), pool, mem, unallocated, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon3_LoopHead:
    assume linear_mem_available
       == linear_mem_MapOr(dom(local), linear_mem_MapConstBool(false));
    assume pool == og_global_old_pool;
    assume mem == og_global_old_mem;
    assume unallocated == og_global_old_unallocated;
    assume pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(local), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    assert PoolInv(unallocated, pool);
    goto anon3_LoopDone, anon3_LoopBody;

  anon3_LoopBody:
    goto anon3_LoopBody0, CallToYieldProc;

  anon3_LoopDone:
    goto anon2;

  anon2:
    goto anon20, CallToYieldProc;

  anon012:
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapOr(dom(local), linear_mem_MapConstBool(false)), pool, mem, unallocated, pendingAsyncMultiset;
    goto anon3_LoopHead;

  anon08:
    call o := Read_1(local, i);
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapOr(dom(local), linear_mem_MapConstBool(false)), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(local), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon012, CallToYieldProc;

  anon04:
    call local := Write_1(local_in, i, 42);
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapOr(dom(local), linear_mem_MapConstBool(false)), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(local), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon08, CallToYieldProc;

  anon00:
    call og_YieldMem_1_Dummy_1(local_in, i);
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapOr(dom(local_in), linear_mem_MapConstBool(false)), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(local_in), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon04, CallToYieldProc;

  anon3_LoopBody20:
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapOr(dom(local), linear_mem_MapConstBool(false)), pool, mem, unallocated, pendingAsyncMultiset;
    goto anon3_LoopHead;

  anon3_LoopBody16:
    call og_Yield_1_Dummy_1();
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapOr(dom(local), linear_mem_MapConstBool(false)), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(local), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon3_LoopBody20, CallToYieldProc;

  anon3_LoopBody12:
    call Free_1(l, y);
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapOr(dom(local), linear_mem_MapConstBool(false)), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(local), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon3_LoopBody16, CallToYieldProc;

  anon3_LoopBody8:
    call o := Read_1(l, y);
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapOr(dom(l), linear_mem_MapOr(dom(local), linear_mem_MapConstBool(false))), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(local), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(3)))
           == linear_mem_MapConstBool(true));
    goto anon3_LoopBody12, CallToYieldProc;

  anon3_LoopBody4:
    call l := Write_1(l, y, 42);
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapOr(dom(l), linear_mem_MapOr(dom(local), linear_mem_MapConstBool(false))), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(local), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(3)))
           == linear_mem_MapConstBool(true));
    goto anon3_LoopBody8, CallToYieldProc;

  anon3_LoopBody0:
    call l, y := Alloc_1();
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapOr(dom(l), linear_mem_MapOr(dom(local), linear_mem_MapConstBool(false))), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(local), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(3)))
           == linear_mem_MapConstBool(true));
    goto anon3_LoopBody4, CallToYieldProc;

  anon24:
    return;

  anon20:
    call og_Yield_1_Dummy_1();
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapOr(dom(local), linear_mem_MapConstBool(false)), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(local), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon24, CallToYieldProc;

  CallToYieldProc:
    call og_yield_1(linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation Alloc_1() returns (l: lmap, i: int)
{
  var og_global_old_pool: lmap;
  var og_global_old_mem: [int]int;
  var og_global_old_unallocated: [int]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;
  var og_old_l: lmap;
  var og_old_i: int;
  var linear_mem_available: [int]bool;

  /*** structured program:
    call Yield();
    call i := PickAddr();
    call l := AllocLinear(i);
    call YieldMem(l, i);
  **** end structured program */

  og_init:
    og_pc, og_ok, linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset, og_old_l, og_old_i := false, false, linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset, l, i;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon020:
    assert og_pc
       || 
      (pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (exists #tmp_0_second_m: [int]int :: 
        pool == Remove(og_global_old_pool, i)
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && l == Add(Empty(#tmp_0_second_m), i)
           && i == i
           && dom(og_global_old_pool)[i]);
    assert og_pc
       ==> pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && l == og_old_l
         && i == og_old_i;
    og_pc, og_ok := pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (exists #tmp_0_second_m: [int]int :: 
        pool == Remove(og_global_old_pool, i)
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && l == Add(Empty(#tmp_0_second_m), i)
           && i == i
           && dom(og_global_old_pool)[i]);
    assert og_ok;
    return;

  anon012:
    assert og_pc
       || 
      (pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (exists #tmp_0_second_m: [int]int :: 
        pool == Remove(og_global_old_pool, i)
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && l == Add(Empty(#tmp_0_second_m), i)
           && i == i
           && dom(og_global_old_pool)[i]);
    assert og_pc
       ==> pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && l == og_old_l
         && i == og_old_i;
    og_pc, og_ok := pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (exists #tmp_0_second_m: [int]int :: 
        pool == Remove(og_global_old_pool, i)
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && l == Add(Empty(#tmp_0_second_m), i)
           && i == i
           && dom(og_global_old_pool)[i]);
    call YieldMem_1(l, i);
    assume og_pc || true;
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset, og_old_l, og_old_i := linear_mem_MapOr(dom(l), linear_mem_MapConstBool(false)), pool, mem, unallocated, pendingAsyncMultiset, l, i;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon020, CallToYieldProc;

  anon00:
    assert og_pc
       || 
      (pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (exists #tmp_0_second_m: [int]int :: 
        pool == Remove(og_global_old_pool, i)
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && l == Add(Empty(#tmp_0_second_m), i)
           && i == i
           && dom(og_global_old_pool)[i]);
    assert og_pc
       ==> pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && l == og_old_l
         && i == og_old_i;
    og_pc, og_ok := pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (exists #tmp_0_second_m: [int]int :: 
        pool == Remove(og_global_old_pool, i)
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && l == Add(Empty(#tmp_0_second_m), i)
           && i == i
           && dom(og_global_old_pool)[i]);
    call Yield_1();
    assume og_pc || true;
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset, og_old_l, og_old_i := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset, l, i;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    call i := atomic_PickAddr_1();
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    call l := AllocLinear(i);
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon012, CallToYieldProc;

  CallToYieldProc:
    call og_yield_1(linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation Free_1(l: lmap, i: int)
{
  var og_global_old_pool: lmap;
  var og_global_old_mem: [int]int;
  var og_global_old_unallocated: [int]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;
  var linear_mem_available: [int]bool;

  /*** structured program:
    call Yield();
    call FreeLinear(l, i);
    call ReturnAddr(i);
    call Yield();
  **** end structured program */

  og_init:
    og_pc, og_ok, linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := false, false, linear_mem_MapOr(dom(l), linear_mem_MapConstBool(false)), pool, mem, unallocated, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon020:
    assert og_pc
       || 
      (pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (pool == Add(og_global_old_pool, i)
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_pc
       ==> pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (pool == Add(og_global_old_pool, i)
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_ok;
    return;

  anon012:
    assert og_pc
       || 
      (pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (pool == Add(og_global_old_pool, i)
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_pc
       ==> pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (pool == Add(og_global_old_pool, i)
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    call Yield_1();
    assume og_pc || dom(l)[i];
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    goto anon020, CallToYieldProc;

  anon00:
    assert og_pc
       || 
      (pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (pool == Add(og_global_old_pool, i)
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_pc
       ==> pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (pool == Add(og_global_old_pool, i)
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    call Yield_1();
    assume og_pc || dom(l)[i];
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapOr(dom(l), linear_mem_MapConstBool(false)), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    call FreeLinear(l, i);
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    call atomic_ReturnAddr_1(i);
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    goto anon012, CallToYieldProc;

  CallToYieldProc:
    call og_yield_1(linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation Read_1(l: lmap, i: int) returns (o: int)
{
  var og_global_old_pool: lmap;
  var og_global_old_mem: [int]int;
  var og_global_old_unallocated: [int]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;
  var og_old_o: int;
  var linear_mem_available: [int]bool;

  /*** structured program:
    call YieldMem(l, i);
    call o := ReadLow(i);
    call YieldMem(l, i);
  **** end structured program */

  og_init:
    og_pc, og_ok, linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset, og_old_o := false, false, linear_mem_MapOr(dom(l), linear_mem_MapConstBool(false)), pool, mem, unallocated, pendingAsyncMultiset, o;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon018:
    assert og_pc
       || 
      (pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (
        pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && o == map(l)[i]);
    assert og_pc
       ==> pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && o == og_old_o;
    og_pc, og_ok := pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (
        pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && o == map(l)[i]);
    assert og_ok;
    return;

  anon010:
    assert og_pc
       || 
      (pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (
        pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && o == map(l)[i]);
    assert og_pc
       ==> pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && o == og_old_o;
    og_pc, og_ok := pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (
        pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && o == map(l)[i]);
    call YieldMem_1(l, i);
    assume og_pc || dom(l)[i];
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset, og_old_o := linear_mem_MapOr(dom(l), linear_mem_MapConstBool(false)), pool, mem, unallocated, pendingAsyncMultiset, o;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon018, CallToYieldProc;

  anon00:
    assert og_pc
       || 
      (pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (
        pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && o == map(l)[i]);
    assert og_pc
       ==> pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && o == og_old_o;
    og_pc, og_ok := pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (
        pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && o == map(l)[i]);
    call YieldMem_1(l, i);
    assume og_pc || dom(l)[i];
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset, og_old_o := linear_mem_MapOr(dom(l), linear_mem_MapConstBool(false)), pool, mem, unallocated, pendingAsyncMultiset, o;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    call o := atomic_ReadLow_1(i);
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon010, CallToYieldProc;

  CallToYieldProc:
    call og_yield_1(linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation Write_1(l: lmap, i: int, o: int) returns (l': lmap)
{
  var og_global_old_pool: lmap;
  var og_global_old_mem: [int]int;
  var og_global_old_unallocated: [int]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;
  var og_old_l': lmap;
  var linear_mem_available: [int]bool;

  /*** structured program:
    call YieldMem(l, i);
    call WriteLow(i, o);
    call l' := WriteLinear(l, i, o);
    call YieldMem(l', i);
  **** end structured program */

  og_init:
    og_pc, og_ok, linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset, og_old_l' := false, false, linear_mem_MapOr(dom(l), linear_mem_MapConstBool(false)), pool, mem, unallocated, pendingAsyncMultiset, l';
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon020:
    assert og_pc
       || 
      (pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (
        pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && l' == cons(dom(l), map(l)[i := o]));
    assert og_pc
       ==> pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && l' == og_old_l';
    og_pc, og_ok := pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (
        pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && l' == cons(dom(l), map(l)[i := o]));
    assert og_ok;
    return;

  anon012:
    assert og_pc
       || 
      (pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (
        pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && l' == cons(dom(l), map(l)[i := o]));
    assert og_pc
       ==> pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && l' == og_old_l';
    og_pc, og_ok := pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (
        pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && l' == cons(dom(l), map(l)[i := o]));
    call YieldMem_1(l', i);
    assume og_pc || dom(l)[i];
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset, og_old_l' := linear_mem_MapOr(dom(l'), linear_mem_MapConstBool(false)), pool, mem, unallocated, pendingAsyncMultiset, l';
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l'), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon020, CallToYieldProc;

  anon00:
    assert og_pc
       || 
      (pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (
        pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && l' == cons(dom(l), map(l)[i := o]));
    assert og_pc
       ==> pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && l' == og_old_l';
    og_pc, og_ok := pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (
        pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && l' == cons(dom(l), map(l)[i := o]));
    call YieldMem_1(l, i);
    assume og_pc || dom(l)[i];
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset, og_old_l' := linear_mem_MapOr(dom(l), linear_mem_MapConstBool(false)), pool, mem, unallocated, pendingAsyncMultiset, l';
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    call atomic_WriteLow_1(i, o);
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    call l' := WriteLinear(l, i, o);
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l'), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon012, CallToYieldProc;

  CallToYieldProc:
    call og_yield_1(linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation Yield_1()
{
  var og_global_old_pool: lmap;
  var og_global_old_mem: [int]int;
  var og_global_old_unallocated: [int]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;
  var linear_mem_available: [int]bool;

  /*** structured program:
    yield;
    assert PoolInv(unallocated, pool);
  **** end structured program */

  og_init:
    og_pc, og_ok, linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := false, false, linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    assert PoolInv(unallocated, pool);
    goto anon02, CallToYieldProc;

  anon011:
    assert og_pc
       || 
      (pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_pc
       ==> pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_ok;
    return;

  anon02:
    assert og_pc
       || 
      (pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_pc
       ==> pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    havoc pool, mem, unallocated, pendingAsyncMultiset;
    assume true;
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    assume PoolInv(unallocated, pool);
    goto anon011, CallToYieldProc;

  CallToYieldProc:
    call og_yield_1(linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation YieldMem_1(l: lmap, i: int)
{
  var og_global_old_pool: lmap;
  var og_global_old_mem: [int]int;
  var og_global_old_unallocated: [int]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;
  var linear_mem_available: [int]bool;

  /*** structured program:
    yield;
    assert PoolInv(unallocated, pool);
    assert dom(l)[i] && map(l)[i] == mem[i];
  **** end structured program */

  og_init:
    og_pc, og_ok, linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := false, false, linear_mem_MapOr(dom(l), linear_mem_MapConstBool(false)), pool, mem, unallocated, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    assert PoolInv(unallocated, pool);
    assert dom(l)[i] && map(l)[i] == mem[i];
    goto anon03, CallToYieldProc;

  anon013:
    assert og_pc
       || 
      (pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_pc
       ==> pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_ok;
    return;

  anon03:
    assert og_pc
       || 
      (pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_pc
       ==> pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (pool == og_global_old_pool
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    havoc pool, mem, unallocated, pendingAsyncMultiset;
    assume true;
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapOr(dom(l), linear_mem_MapConstBool(false)), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    assume PoolInv(unallocated, pool);
    assume dom(l)[i] && map(l)[i] == mem[i];
    goto anon013, CallToYieldProc;

  CallToYieldProc:
    call og_yield_1(linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation Dummy_1()
{
  var og_global_old_pool: lmap;
  var og_global_old_mem: [int]int;
  var og_global_old_unallocated: [int]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_mem_available: [int]bool;

  /*** structured program:
    yield;
  **** end structured program */

  og_init:
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    goto anon01, CallToYieldProc;

  anon05:
    return;

  anon01:
    havoc pool, mem, unallocated, pendingAsyncMultiset;
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    goto anon05, CallToYieldProc;

  CallToYieldProc:
    call og_yield_1(linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



procedure {:inline 1} Impl_YieldChecker_Yield_1(linear_mem_in: [int]bool, 
    og_global_old_pool: lmap, 
    og_global_old_mem: [int]int, 
    og_global_old_unallocated: [int]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_YieldMem_1(linear_mem_in: [int]bool, 
    og_global_old_pool: lmap, 
    og_global_old_mem: [int]int, 
    og_global_old_unallocated: [int]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_Dummy_1(linear_mem_in: [int]bool, 
    og_global_old_pool: lmap, 
    og_global_old_mem: [int]int, 
    og_global_old_unallocated: [int]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



implementation {:inline 1} Impl_YieldChecker_Yield_1(linear_mem_in: [int]bool, 
    og_global_old_pool: lmap, 
    og_global_old_mem: [int]int, 
    og_global_old_unallocated: [int]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var og_local_old_pool: lmap;
  var og_local_old_mem: [int]int;
  var og_local_old_unallocated: [int]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_in, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(og_global_old_pool), 
            linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    assume PoolInv(og_global_old_unallocated, og_global_old_pool);
    assert PoolInv(unallocated, pool);
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_YieldMem_1(linear_mem_in: [int]bool, 
    og_global_old_pool: lmap, 
    og_global_old_mem: [int]int, 
    og_global_old_unallocated: [int]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var l: lmap;
  var i: int;
  var og_local_old_pool: lmap;
  var og_local_old_mem: [int]int;
  var og_local_old_unallocated: [int]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_in, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(og_global_old_pool), 
            linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    assume PoolInv(og_global_old_unallocated, og_global_old_pool);
    assume dom(l)[i] && map(l)[i] == og_global_old_mem[i];
    assert PoolInv(unallocated, pool);
    assert dom(l)[i] && map(l)[i] == mem[i];
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_Dummy_1(linear_mem_in: [int]bool, 
    og_global_old_pool: lmap, 
    og_global_old_mem: [int]int, 
    og_global_old_unallocated: [int]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var og_local_old_pool: lmap;
  var og_local_old_mem: [int]int;
  var og_local_old_unallocated: [int]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_in, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(og_global_old_pool), 
            linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    assume false;
    return;
}



procedure og_Yield_1_Dummy_1();
  requires PoolInv(unallocated, pool);
  modifies pool, mem, unallocated, pendingAsyncMultiset;
  ensures PoolInv(unallocated, pool);



procedure DummyAsyncTarget_Thread_1(local_in: lmap, i: int);
  requires PoolInv(unallocated, pool);
  requires dom(local_in)[i] && map(local_in)[i] == mem[i];
  free requires (exists partition_mem: [int]int :: 
    linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
         == linear_mem_MapConstBool(true)
       && linear_mem_MapImp(dom(local_in), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
         == linear_mem_MapConstBool(true));



procedure og_YieldMem_1_Dummy_1(og_0_l: lmap, og_0_i: int);
  requires PoolInv(unallocated, pool);
  requires dom(og_0_l)[og_0_i] && map(og_0_l)[og_0_i] == mem[og_0_i];
  free requires (exists partition_mem: [int]int :: 
    linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
         == linear_mem_MapConstBool(true)
       && linear_mem_MapImp(dom(og_0_l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
         == linear_mem_MapConstBool(true));
  modifies pool, mem, unallocated, pendingAsyncMultiset;
  ensures PoolInv(unallocated, pool);
  ensures dom(og_0_l)[og_0_i] && map(og_0_l)[og_0_i] == mem[og_0_i];



procedure {:inline 1} og_yield_1(linear_mem_in: [int]bool, 
    og_global_old_pool: lmap, 
    og_global_old_mem: [int]int, 
    og_global_old_unallocated: [int]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



implementation {:inline 1} og_yield_1(linear_mem_in: [int]bool, 
    og_global_old_pool: lmap, 
    og_global_old_mem: [int]int, 
    og_global_old_unallocated: [int]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{

  enter:
    goto L_0, L_1, L_2;

  L_0:
    call Impl_YieldChecker_Yield_1(linear_mem_in, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset);
    return;

  L_1:
    call Impl_YieldChecker_YieldMem_1(linear_mem_in, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset);
    return;

  L_2:
    call Impl_YieldChecker_Dummy_1(linear_mem_in, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset);
    return;
}



procedure Main_2();
  modifies pool, mem, unallocated, pendingAsyncMultiset;



procedure Thread_2(local_in: lmap, i: int);
  requires dom(local_in)[i];
  free requires (exists partition_mem: [int]int :: 
    linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
         == linear_mem_MapConstBool(true)
       && linear_mem_MapImp(dom(local_in), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
         == linear_mem_MapConstBool(true));
  modifies pool, mem, unallocated, pendingAsyncMultiset;



procedure Dummy_2();
  modifies pool, mem, unallocated, pendingAsyncMultiset;



implementation Main_2()
{
  var l: lmap;
  var i: int;
  var og_global_old_pool: lmap;
  var og_global_old_mem: [int]int;
  var og_global_old_unallocated: [int]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;
  var linear_mem_available: [int]bool;
  var og_pc_anon3_LoopHead: bool;
  var og_ok_anon3_LoopHead: bool;

  /*** structured program:
    while (*)
      invariant PoolInv(unallocated, pool);
    {
        call l, i := Alloc();
        async call Thread(l, i);
    }

  **** end structured program */

  og_init:
    og_pc, og_pc_anon3_LoopHead, og_ok, og_ok_anon3_LoopHead, linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := false, false, false, false, linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon3_LoopHead:
    assert og_pc_anon3_LoopHead == og_pc;
    assert og_ok_anon3_LoopHead ==> og_ok;
    assume linear_mem_available == linear_mem_MapConstBool(false);
    assume pool == og_global_old_pool;
    assume mem == og_global_old_mem;
    assume unallocated == og_global_old_unallocated;
    assume pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    goto anon3_LoopDone, anon3_LoopBody;

  anon3_LoopBody:
    call l, i := atomic_Alloc_2();
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon3_LoopBody2, CallToYieldProc;

  anon3_LoopDone:
    goto anon2;

  anon2:
    goto anon20, CallToYieldProc;

  anon08:
    assert og_pc
       || 
      pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assert og_pc ==> pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := pendingAsyncMultiset == og_global_old_pendingAsyncMultiset ==> og_pc, og_ok || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc_anon3_LoopHead, og_ok_anon3_LoopHead := og_pc, og_ok;
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    goto anon3_LoopHead;

  anon00:
    assert og_pc
       || 
      pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assert og_pc ==> pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := pendingAsyncMultiset == og_global_old_pendingAsyncMultiset ==> og_pc, og_ok || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    call og_skip_dummy_Yield_Dummy_2();
    assume true;
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    goto anon08, CallToYieldProc;

  anon3_LoopBody17:
    assert og_pc
       || 
      pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assert og_pc ==> pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := pendingAsyncMultiset == og_global_old_pendingAsyncMultiset ==> og_pc, og_ok || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    goto anon3_LoopHead;

  anon3_LoopBody9:
    assert og_pc
       || 
      pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assert og_pc ==> pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := pendingAsyncMultiset == og_global_old_pendingAsyncMultiset ==> og_pc, og_ok || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    call og_skip_dummy_Yield_Dummy_2();
    assume true;
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    goto anon3_LoopBody17, CallToYieldProc;

  anon3_LoopBody2:
    assert og_pc
       || 
      pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assert og_pc ==> pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := pendingAsyncMultiset == og_global_old_pendingAsyncMultiset ==> og_pc, og_ok || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    call DummyAsyncTarget_Thread_2(l, i);
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    goto anon3_LoopBody9, CallToYieldProc;

  anon28:
    assert og_pc
       || 
      pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assert og_pc ==> pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := pendingAsyncMultiset == og_global_old_pendingAsyncMultiset ==> og_pc, og_ok || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assert og_ok;
    return;

  anon20:
    assert og_pc
       || 
      pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assert og_pc ==> pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := pendingAsyncMultiset == og_global_old_pendingAsyncMultiset ==> og_pc, og_ok || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    call og_skip_dummy_Yield_Dummy_2();
    assume true;
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    goto anon28, CallToYieldProc;

  CallToYieldProc:
    call og_yield_2(linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation Thread_2(local_in: lmap, i: int)
{
  var y: int;
  var o: int;
  var local: lmap;
  var l: lmap;
  var og_global_old_pool: lmap;
  var og_global_old_mem: [int]int;
  var og_global_old_unallocated: [int]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;
  var linear_mem_available: [int]bool;
  var og_pc_anon3_LoopHead: bool;
  var og_ok_anon3_LoopHead: bool;

  /*** structured program:
    call local := Write(local_in, i, 42);
    call o := Read(local, i);
    assert o == 42;
    while (*)
      invariant PoolInv(unallocated, pool);
    {
        call l, y := Alloc();
        call l := Write(l, y, 42);
        call o := Read(l, y);
        assert o == 42;
        call Free(l, y);
    }

  **** end structured program */

  og_init:
    og_pc, og_pc_anon3_LoopHead, og_ok, og_ok_anon3_LoopHead, linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := false, false, false, false, linear_mem_MapOr(dom(local_in), linear_mem_MapConstBool(false)), pool, mem, unallocated, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon3_LoopHead:
    assert og_pc_anon3_LoopHead == og_pc;
    assert og_ok_anon3_LoopHead ==> og_ok;
    assume linear_mem_available
       == linear_mem_MapOr(dom(local), linear_mem_MapConstBool(false));
    assume pool == og_global_old_pool;
    assume mem == og_global_old_mem;
    assume unallocated == og_global_old_unallocated;
    assume pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(local), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon3_LoopDone, anon3_LoopBody;

  anon3_LoopBody:
    call l, y := atomic_Alloc_2();
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(local), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(3)))
           == linear_mem_MapConstBool(true));
    // <<< injected gate
    assert dom(l)[y];
    // injected gate >>>
    call l := atomic_Write_2(l, y, 42);
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(local), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(3)))
           == linear_mem_MapConstBool(true));
    // <<< injected gate
    assert dom(l)[y];
    // injected gate >>>
    call o := atomic_Read_2(l, y);
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(local), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(l), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(3)))
           == linear_mem_MapConstBool(true));
    assert o == 42;
    // <<< injected gate
    assert dom(l)[y];
    // injected gate >>>
    call atomic_Free_2(l, y);
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(local), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon3_LoopBody18, CallToYieldProc;

  anon3_LoopDone:
    goto anon2;

  anon2:
    goto anon20, CallToYieldProc;

  anon019:
    assert og_pc
       || 
      pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assert og_pc ==> pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := pendingAsyncMultiset == og_global_old_pendingAsyncMultiset ==> og_pc, og_ok || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc_anon3_LoopHead, og_ok_anon3_LoopHead := og_pc, og_ok;
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapOr(dom(local), linear_mem_MapConstBool(false)), pool, mem, unallocated, pendingAsyncMultiset;
    goto anon3_LoopHead;

  anon00:
    assert og_pc
       || 
      pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assert og_pc ==> pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := pendingAsyncMultiset == og_global_old_pendingAsyncMultiset ==> og_pc, og_ok || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    call og_skip_dummy_YieldMem_Dummy_2(local_in, i);
    assume true;
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapOr(dom(local_in), linear_mem_MapConstBool(false)), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(local_in), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    // <<< injected gate
    assert dom(local_in)[i];
    // injected gate >>>
    call local := atomic_Write_2(local_in, i, 42);
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(local), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    // <<< injected gate
    assert dom(local)[i];
    // injected gate >>>
    call o := atomic_Read_2(local, i);
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(local), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    assert o == 42;
    goto anon019, CallToYieldProc;

  anon3_LoopBody26:
    assert og_pc
       || 
      pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assert og_pc ==> pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := pendingAsyncMultiset == og_global_old_pendingAsyncMultiset ==> og_pc, og_ok || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapOr(dom(local), linear_mem_MapConstBool(false)), pool, mem, unallocated, pendingAsyncMultiset;
    goto anon3_LoopHead;

  anon3_LoopBody18:
    assert og_pc
       || 
      pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assert og_pc ==> pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := pendingAsyncMultiset == og_global_old_pendingAsyncMultiset ==> og_pc, og_ok || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    call og_skip_dummy_Yield_Dummy_2();
    assume true;
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapOr(dom(local), linear_mem_MapConstBool(false)), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(local), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon3_LoopBody26, CallToYieldProc;

  anon28:
    assert og_pc
       || 
      pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assert og_pc ==> pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := pendingAsyncMultiset == og_global_old_pendingAsyncMultiset ==> og_pc, og_ok || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assert og_ok;
    return;

  anon20:
    assert og_pc
       || 
      pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assert og_pc ==> pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := pendingAsyncMultiset == og_global_old_pendingAsyncMultiset ==> og_pc, og_ok || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    call og_skip_dummy_Yield_Dummy_2();
    assume true;
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapOr(dom(local), linear_mem_MapConstBool(false)), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(local), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(2)))
           == linear_mem_MapConstBool(true));
    goto anon28, CallToYieldProc;

  CallToYieldProc:
    call og_yield_2(linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation Dummy_2()
{
  var og_global_old_pool: lmap;
  var og_global_old_mem: [int]int;
  var og_global_old_unallocated: [int]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;
  var linear_mem_available: [int]bool;

  /*** structured program:
    yield;
  **** end structured program */

  og_init:
    og_pc, og_ok, linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := false, false, linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    goto anon01, CallToYieldProc;

  anon09:
    assert og_pc
       || 
      pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assert og_pc ==> pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := pendingAsyncMultiset == og_global_old_pendingAsyncMultiset ==> og_pc, og_ok || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assert og_ok;
    return;

  anon01:
    assert og_pc
       || 
      pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assert og_pc ==> pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := pendingAsyncMultiset == og_global_old_pendingAsyncMultiset ==> og_pc, og_ok || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    havoc pool, mem, unallocated, pendingAsyncMultiset;
    assume true;
    linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset := linear_mem_MapConstBool(false), pool, mem, unallocated, pendingAsyncMultiset;
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_hole, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    goto anon09, CallToYieldProc;

  CallToYieldProc:
    call og_yield_2(linear_mem_available, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



procedure {:inline 1} Impl_YieldChecker_Dummy_2(linear_mem_in: [int]bool, 
    og_global_old_pool: lmap, 
    og_global_old_mem: [int]int, 
    og_global_old_unallocated: [int]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



implementation {:inline 1} Impl_YieldChecker_Dummy_2(linear_mem_in: [int]bool, 
    og_global_old_pool: lmap, 
    og_global_old_mem: [int]int, 
    og_global_old_unallocated: [int]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var og_local_old_pool: lmap;
  var og_local_old_mem: [int]int;
  var og_local_old_unallocated: [int]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_mem: [int]int :: 
      linear_mem_MapImp(linear_mem_in, linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
           == linear_mem_MapConstBool(true)
         && linear_mem_MapImp(dom(og_global_old_pool), 
            linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
           == linear_mem_MapConstBool(true));
    assume false;
    return;
}



procedure og_skip_dummy_Yield_Dummy_2();
  modifies pool, mem, unallocated, pendingAsyncMultiset;



procedure DummyAsyncTarget_Thread_2(local_in: lmap, i: int);
  requires dom(local_in)[i];
  free requires (exists partition_mem: [int]int :: 
    linear_mem_MapImp(dom(pool), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(0)))
         == linear_mem_MapConstBool(true)
       && linear_mem_MapImp(dom(local_in), linear_mem_MapEq(partition_mem, linear_mem_MapConstInt(1)))
         == linear_mem_MapConstBool(true));



procedure og_skip_dummy_YieldMem_Dummy_2(og_0_l: lmap, og_0_i: int);
  modifies pool, mem, unallocated, pendingAsyncMultiset;



procedure {:inline 1} og_yield_2(linear_mem_in: [int]bool, 
    og_global_old_pool: lmap, 
    og_global_old_mem: [int]int, 
    og_global_old_unallocated: [int]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



implementation {:inline 1} og_yield_2(linear_mem_in: [int]bool, 
    og_global_old_pool: lmap, 
    og_global_old_mem: [int]int, 
    og_global_old_unallocated: [int]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{

  enter:
    goto L_0;

  L_0:
    call Impl_YieldChecker_Dummy_2(linear_mem_in, og_global_old_pool, og_global_old_mem, og_global_old_unallocated, og_global_old_pendingAsyncMultiset);
    return;
}


