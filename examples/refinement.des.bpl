// Boogie program verifier version 2.4.1.10503, Copyright (c) 2003-2014, Microsoft.
// Command Line Options: -nologo -useArrayTheory /noWitnessInference /noCommutativityTriggers /CivlDesugaredFile:refinement.des.bpl refinement.bpl

var x: int;

type {:datatype} PendingAsync;

var pendingAsyncMultiset: [PendingAsync]int;

function {:constructor} PendingAsync_set_x(v: int) : PendingAsync;

procedure {:inline 1} AddPendingAsync_set_x(v: int);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_set_x(v: int)
{

  L:
    pendingAsyncMultiset[PendingAsync_set_x(v)] := pendingAsyncMultiset[PendingAsync_set_x(v)] + 1;
    return;
}



function {:constructor} PendingAsync_pos() : PendingAsync;

procedure {:inline 1} AddPendingAsync_pos();
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_pos()
{

  L:
    pendingAsyncMultiset[PendingAsync_pos()] := pendingAsyncMultiset[PendingAsync_pos()] + 1;
    return;
}



function {:constructor} PendingAsync_p() : PendingAsync;

procedure {:inline 1} AddPendingAsync_p();
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_p()
{

  L:
    pendingAsyncMultiset[PendingAsync_p()] := pendingAsyncMultiset[PendingAsync_p()] + 1;
    return;
}



function {:constructor} PendingAsync_q() : PendingAsync;

procedure {:inline 1} AddPendingAsync_q();
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_q()
{

  L:
    pendingAsyncMultiset[PendingAsync_q()] := pendingAsyncMultiset[PendingAsync_q()] + 1;
    return;
}



procedure {:inline 1} SET_X_1(v: int);
  modifies x;



procedure {:inline 1} POS_1();
  modifies x;



procedure {:inline 1} STUPID_POS_1();
  modifies x;



implementation {:inline 1} SET_X_1(v: int)
{
  /*** structured program:
    x := v;
  **** end structured program */

  anon0:
    x := v;
    return;
}



implementation {:inline 1} POS_1()
{
  var l: int;

  /*** structured program:
    assume l > 0;
    x := l;
  **** end structured program */

  anon0:
    assume l > 0;
    x := l;
    return;
}



implementation {:inline 1} STUPID_POS_1()
{
  var l: int;

  /*** structured program:
    assume l >= 0;
    x := l + 1;
  **** end structured program */

  anon0:
    assume l >= 0;
    x := l + 1;
    return;
}



procedure {:inline 1} SET_X_2(v: int);
  modifies x;



procedure {:inline 1} POS_2();
  modifies x;



procedure {:inline 1} STUPID_POS_2();
  modifies x;



implementation {:inline 1} SET_X_2(v: int)
{
  /*** structured program:
    x := v;
  **** end structured program */

  anon0:
    x := v;
    return;
}



implementation {:inline 1} POS_2()
{
  var l: int;

  /*** structured program:
    assume l > 0;
    x := l;
  **** end structured program */

  anon0:
    assume l > 0;
    x := l;
    return;
}



implementation {:inline 1} STUPID_POS_2()
{
  var l: int;

  /*** structured program:
    assume l >= 0;
    x := l + 1;
  **** end structured program */

  anon0:
    assume l >= 0;
    x := l + 1;
    return;
}



procedure set_x_0(v: int);
  modifies x, pendingAsyncMultiset;



procedure pos_0();
  modifies x, pendingAsyncMultiset;



procedure p_0();
  modifies x, pendingAsyncMultiset;



procedure q_0();
  modifies x, pendingAsyncMultiset;



implementation p_0()
{
  var og_global_old_x: int;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;

  /*** structured program:
    yield;
    call set_x(1);
    yield;
  **** end structured program */

  og_init:
    og_global_old_x, og_global_old_pendingAsyncMultiset := x, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon09:
    return;

  anon06:
    havoc x, pendingAsyncMultiset;
    og_global_old_x, og_global_old_pendingAsyncMultiset := x, pendingAsyncMultiset;
    goto anon09, CallToYieldProc;

  anon03:
    call set_x_0(1);
    og_global_old_x, og_global_old_pendingAsyncMultiset := x, pendingAsyncMultiset;
    goto anon06, CallToYieldProc;

  anon00:
    havoc x, pendingAsyncMultiset;
    og_global_old_x, og_global_old_pendingAsyncMultiset := x, pendingAsyncMultiset;
    goto anon03, CallToYieldProc;

  CallToYieldProc:
    call og_yield_0(og_global_old_x, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation q_0()
{
  var og_global_old_x: int;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;

  /*** structured program:
    yield;
    call set_x(1);
    yield;
  **** end structured program */

  og_init:
    og_global_old_x, og_global_old_pendingAsyncMultiset := x, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon09:
    return;

  anon06:
    havoc x, pendingAsyncMultiset;
    og_global_old_x, og_global_old_pendingAsyncMultiset := x, pendingAsyncMultiset;
    goto anon09, CallToYieldProc;

  anon03:
    call set_x_0(1);
    og_global_old_x, og_global_old_pendingAsyncMultiset := x, pendingAsyncMultiset;
    goto anon06, CallToYieldProc;

  anon00:
    havoc x, pendingAsyncMultiset;
    og_global_old_x, og_global_old_pendingAsyncMultiset := x, pendingAsyncMultiset;
    goto anon03, CallToYieldProc;

  CallToYieldProc:
    call og_yield_0(og_global_old_x, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



procedure {:inline 1} og_yield_0(og_global_old_x: int, og_global_old_pendingAsyncMultiset: [PendingAsync]int);



implementation {:inline 1} og_yield_0(og_global_old_x: int, og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{

  enter:
    return;
}



procedure p_1();
  modifies x, pendingAsyncMultiset;



procedure q_1();
  modifies x, pendingAsyncMultiset;



implementation p_1()
{
  var og_global_old_x: int;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;

  /*** structured program:
    yield;
    call set_x(1);
    yield;
  **** end structured program */

  og_init:
    og_pc, og_ok, og_global_old_x, og_global_old_pendingAsyncMultiset := false, false, x, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon015:
    assert og_pc
       || 
      (x == og_global_old_x
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (x == x && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset && x > 0);
    assert og_pc
       ==> x == og_global_old_x
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := x == og_global_old_x
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (x == x && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset && x > 0);
    assert og_ok;
    return;

  anon08:
    assert og_pc
       || 
      (x == og_global_old_x
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (x == x && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset && x > 0);
    assert og_pc
       ==> x == og_global_old_x
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := x == og_global_old_x
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (x == x && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset && x > 0);
    havoc x, pendingAsyncMultiset;
    assume og_pc || true;
    og_global_old_x, og_global_old_pendingAsyncMultiset := x, pendingAsyncMultiset;
    goto anon015, CallToYieldProc;

  anon00:
    assert og_pc
       || 
      (x == og_global_old_x
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (x == x && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset && x > 0);
    assert og_pc
       ==> x == og_global_old_x
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := x == og_global_old_x
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (x == x && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset && x > 0);
    havoc x, pendingAsyncMultiset;
    assume og_pc || true;
    og_global_old_x, og_global_old_pendingAsyncMultiset := x, pendingAsyncMultiset;
    call SET_X_1(1);
    goto anon08, CallToYieldProc;

  CallToYieldProc:
    call og_yield_1(og_global_old_x, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation q_1()
{
  var og_global_old_x: int;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;

  /*** structured program:
    yield;
    call set_x(1);
    yield;
  **** end structured program */

  og_init:
    og_pc, og_ok, og_global_old_x, og_global_old_pendingAsyncMultiset := false, false, x, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon015:
    assert og_pc
       || 
      (x == og_global_old_x
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (exists #tmp_0_second_l: int :: 
        x == #tmp_0_second_l + 1
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && #tmp_0_second_l >= 0);
    assert og_pc
       ==> x == og_global_old_x
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := x == og_global_old_x
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (exists #tmp_0_second_l: int :: 
        x == #tmp_0_second_l + 1
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && #tmp_0_second_l >= 0);
    assert og_ok;
    return;

  anon08:
    assert og_pc
       || 
      (x == og_global_old_x
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (exists #tmp_0_second_l: int :: 
        x == #tmp_0_second_l + 1
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && #tmp_0_second_l >= 0);
    assert og_pc
       ==> x == og_global_old_x
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := x == og_global_old_x
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (exists #tmp_0_second_l: int :: 
        x == #tmp_0_second_l + 1
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && #tmp_0_second_l >= 0);
    havoc x, pendingAsyncMultiset;
    assume og_pc || true;
    og_global_old_x, og_global_old_pendingAsyncMultiset := x, pendingAsyncMultiset;
    goto anon015, CallToYieldProc;

  anon00:
    assert og_pc
       || 
      (x == og_global_old_x
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (exists #tmp_0_second_l: int :: 
        x == #tmp_0_second_l + 1
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && #tmp_0_second_l >= 0);
    assert og_pc
       ==> x == og_global_old_x
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := x == og_global_old_x
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (exists #tmp_0_second_l: int :: 
        x == #tmp_0_second_l + 1
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && #tmp_0_second_l >= 0);
    havoc x, pendingAsyncMultiset;
    assume og_pc || true;
    og_global_old_x, og_global_old_pendingAsyncMultiset := x, pendingAsyncMultiset;
    call SET_X_1(1);
    goto anon08, CallToYieldProc;

  CallToYieldProc:
    call og_yield_1(og_global_old_x, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



procedure {:inline 1} og_yield_1(og_global_old_x: int, og_global_old_pendingAsyncMultiset: [PendingAsync]int);



implementation {:inline 1} og_yield_1(og_global_old_x: int, og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{

  enter:
    return;
}


