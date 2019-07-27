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
