// Boogie program verifier version 2.4.1.10503, Copyright (c) 2003-2014, Microsoft.
// Command Line Options: /noWitnessInference /noCommutativityTriggers /noVerify /CivlDesugaredFile:desugared_files/Siddharth-queue.desugared.bpl ../Siddharth-queue.bpl

type Method;

type Invoc;

type SeqInvoc;

function Seq_append(s: SeqInvoc, o: Invoc) : SeqInvoc;

type SetInvoc;

function Set_ofSeq(q: SeqInvoc) : SetInvoc;

var lin: SeqInvoc;

var vis: [Invoc]SetInvoc;

type Ref;

type Key;

procedure intro_readLin() returns (s: SetInvoc);
  ensures s == Set_ofSeq(lin);



implementation intro_readLin() returns (s: SetInvoc)
{
  /*** structured program:
    s := Set_ofSeq(lin);
  **** end structured program */

  anon0:
    s := Set_ofSeq(lin);
    return;
}



procedure intro_write_vis(n: Invoc, s: SetInvoc);
  modifies vis;
  ensures vis == old(vis)[n := s];



implementation intro_write_vis(n: Invoc, s: SetInvoc)
{
  /*** structured program:
    vis[n] := s;
  **** end structured program */

  anon0:
    vis[n] := s;
    return;
}



procedure intro_writeLin(n: Invoc);
  modifies lin;
  ensures lin == Seq_append(old(lin), n);



implementation intro_writeLin(n: Invoc)
{
  /*** structured program:
    lin := Seq_append(lin, n);
  **** end structured program */

  anon0:
    lin := Seq_append(lin, n);
    return;
}



type {:datatype} PendingAsync;

var pendingAsyncMultiset: [PendingAsync]int;

function {:constructor} PendingAsync_pop(this: Invoc) : PendingAsync;

procedure {:inline 1} AddPendingAsync_pop(this: Invoc);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_pop(this: Invoc)
{

  L:
    pendingAsyncMultiset[PendingAsync_pop(this)] := pendingAsyncMultiset[PendingAsync_pop(this)] + 1;
    return;
}



procedure {:inline 1} pop_atomic_2(this: Invoc) returns (k: Key);
  modifies lin, vis;



implementation {:inline 1} pop_atomic_2(this: Invoc) returns (k: Key)
{
  var my_vis: SetInvoc;

  /*** structured program:
    lin := Seq_append(lin, this);
    assume my_vis == Set_ofSeq(lin);
    vis[this] := my_vis;
  **** end structured program */

  anon0:
    lin := Seq_append(lin, this);
    assume my_vis == Set_ofSeq(lin);
    vis[this] := my_vis;
    return;
}



procedure pop_1(this: Invoc) returns (k: Key);
  modifies lin, vis, pendingAsyncMultiset;



implementation pop_1(this: Invoc) returns (k: Key)
{
  var my_vis: SetInvoc;
  var og_global_old_lin: SeqInvoc;
  var og_global_old_vis: [Invoc]SetInvoc;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;
  var og_old_k: Key;

  /*** structured program:
    yield;
    call intro_writeLin(this);
    call my_vis := intro_readLin();
    call intro_write_vis(this, my_vis);
    assert my_vis == Set_ofSeq(lin);
    yield;
  **** end structured program */

  og_init:
    og_pc, og_ok, og_global_old_lin, og_global_old_vis, og_global_old_pendingAsyncMultiset, og_old_k := false, false, lin, vis, pendingAsyncMultiset, k;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon018:
    assert og_pc
       || 
      (
        lin == og_global_old_lin
         && vis == og_global_old_vis
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (exists #tmp_0_second_my_vis: SetInvoc :: 
        lin == Seq_append(og_global_old_lin, this)
           && vis == og_global_old_vis[this := #tmp_0_second_my_vis]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && k == k
           && #tmp_0_second_my_vis == Set_ofSeq(Seq_append(og_global_old_lin, this)));
    assert og_pc
       ==> lin == og_global_old_lin
         && vis == og_global_old_vis
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && k == og_old_k;
    og_pc, og_ok := lin == og_global_old_lin
         && vis == og_global_old_vis
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (exists #tmp_0_second_my_vis: SetInvoc :: 
        lin == Seq_append(og_global_old_lin, this)
           && vis == og_global_old_vis[this := #tmp_0_second_my_vis]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && k == k
           && #tmp_0_second_my_vis == Set_ofSeq(Seq_append(og_global_old_lin, this)));
    assert og_ok;
    return;

  anon011:
    assert og_pc
       || 
      (
        lin == og_global_old_lin
         && vis == og_global_old_vis
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (exists #tmp_0_second_my_vis: SetInvoc :: 
        lin == Seq_append(og_global_old_lin, this)
           && vis == og_global_old_vis[this := #tmp_0_second_my_vis]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && k == k
           && #tmp_0_second_my_vis == Set_ofSeq(Seq_append(og_global_old_lin, this)));
    assert og_pc
       ==> lin == og_global_old_lin
         && vis == og_global_old_vis
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && k == og_old_k;
    og_pc, og_ok := lin == og_global_old_lin
         && vis == og_global_old_vis
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (exists #tmp_0_second_my_vis: SetInvoc :: 
        lin == Seq_append(og_global_old_lin, this)
           && vis == og_global_old_vis[this := #tmp_0_second_my_vis]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && k == k
           && #tmp_0_second_my_vis == Set_ofSeq(Seq_append(og_global_old_lin, this)));
    havoc lin, vis, pendingAsyncMultiset;
    assume og_pc || true;
    og_global_old_lin, og_global_old_vis, og_global_old_pendingAsyncMultiset, og_old_k := lin, vis, pendingAsyncMultiset, k;
    goto anon018, CallToYieldProc;

  anon00:
    assert og_pc
       || 
      (
        lin == og_global_old_lin
         && vis == og_global_old_vis
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (exists #tmp_0_second_my_vis: SetInvoc :: 
        lin == Seq_append(og_global_old_lin, this)
           && vis == og_global_old_vis[this := #tmp_0_second_my_vis]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && k == k
           && #tmp_0_second_my_vis == Set_ofSeq(Seq_append(og_global_old_lin, this)));
    assert og_pc
       ==> lin == og_global_old_lin
         && vis == og_global_old_vis
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && k == og_old_k;
    og_pc, og_ok := lin == og_global_old_lin
         && vis == og_global_old_vis
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (exists #tmp_0_second_my_vis: SetInvoc :: 
        lin == Seq_append(og_global_old_lin, this)
           && vis == og_global_old_vis[this := #tmp_0_second_my_vis]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && k == k
           && #tmp_0_second_my_vis == Set_ofSeq(Seq_append(og_global_old_lin, this)));
    havoc lin, vis, pendingAsyncMultiset;
    assume og_pc || true;
    og_global_old_lin, og_global_old_vis, og_global_old_pendingAsyncMultiset, og_old_k := lin, vis, pendingAsyncMultiset, k;
    call intro_writeLin(this);
    call my_vis := intro_readLin();
    call intro_write_vis(this, my_vis);
    assert my_vis == Set_ofSeq(lin);
    goto anon011, CallToYieldProc;

  CallToYieldProc:
    call og_yield_1(og_global_old_lin, og_global_old_vis, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



procedure {:inline 1} og_yield_1(og_global_old_lin: SeqInvoc, 
    og_global_old_vis: [Invoc]SetInvoc, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



implementation {:inline 1} og_yield_1(og_global_old_lin: SeqInvoc, 
    og_global_old_vis: [Invoc]SetInvoc, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{

  enter:
    return;
}


