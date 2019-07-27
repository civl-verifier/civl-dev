// Boogie program verifier version 2.4.1.10503, Copyright (c) 2003-2014, Microsoft.
// Command Line Options: /noWitnessInference /noCommutativityTriggers /noVerify /CivlDesugaredFile:desugared_files_async/2pc.desugared.bpl ../async/2pc.bpl

type Xid = int;

type Mid = int;

const CoordinatorMid: Mid;

axiom CoordinatorMid == 0;

function coordinatorMid(mid: Mid) : bool;

axiom (forall mid: Mid :: 
  { coordinatorMid(mid): bool } 
  coordinatorMid(mid): bool <==> mid == CoordinatorMid);

const numParticipants: int;

axiom 0 < numParticipants;

function participantMid(mid: Mid) : bool;

axiom (forall mid: Mid :: 
  { participantMid(mid): bool } 
  participantMid(mid): bool <==> 1 <= mid && mid <= numParticipants);

type {:datatype} Pair;

function {:constructor} Pair(xid: Xid, mid: Mid) : Pair;

function {:inline} pair(xid: Xid, mid: Mid, p: Pair) : bool
{
  p == Pair(xid, mid) && participantMid(mid#Pair(p))
}

type MState = int;

function {:inline} ABORTED() : int
{
  0
}

function {:inline} UNDECIDED() : int
{
  1
}

function {:inline} COMMITTED() : int
{
  2
}

function {:inline} Aborted(i: MState) : bool
{
  i == ABORTED()
}

function {:inline} Undecided(i: MState) : bool
{
  i == UNDECIDED()
}

function {:inline} Committed(i: MState) : bool
{
  i == COMMITTED()
}

function {:inline} UndecidedOrAborted(i: MState) : bool
{
  Undecided(i) || Aborted(i)
}

function {:inline} UndecidedOrCommitted(i: MState) : bool
{
  Undecided(i) || Committed(i)
}

type XState = [Mid]MState;

type GState = [Xid]XState;

var state: GState;

var votes: [Xid]int;

var B: [Pair]bool;

var AllocatedXids: [Xid]bool;

function {:inline} xUndecided(state: XState) : bool
{
  Undecided(state[CoordinatorMid])
     && (forall i: Mid :: participantMid(i) ==> Undecided(state[i]))
}

function {:inline} xUndecidedOrCommitted(state: XState) : bool
{
  UndecidedOrCommitted(state[CoordinatorMid])
     && (forall i: Mid :: participantMid(i) ==> UndecidedOrCommitted(state[i]))
}

function {:inline} xUndecidedOrAborted(state: XState) : bool
{
  UndecidedOrAborted(state[CoordinatorMid])
     && (forall i: Mid :: participantMid(i) ==> UndecidedOrAborted(state[i]))
}

function {:inline} xConsistent(state: XState) : bool
{
  xUndecidedOrCommitted(state) || xUndecidedOrAborted(state)
}

function {:inline} xNoUndoneDecision(oldState: XState, newState: XState) : bool
{
  (newState[CoordinatorMid] == oldState[CoordinatorMid]
       || Undecided(oldState[CoordinatorMid]))
     && (forall i: Mid :: 
      participantMid(i) ==> newState[i] == oldState[i] || Undecided(oldState[i]))
}

function {:inline} xConsistentExtension(oldState: XState, newState: XState) : bool
{
  xConsistent(newState) && xNoUndoneDecision(oldState, newState)
}

function {:inline} xAllParticipantsInB(xid: Xid, B: [Pair]bool) : bool
{
  (forall mid: Mid :: participantMid(mid) ==> B[Pair(xid, mid)])
}

function {:inline} gUndecided(state: GState) : bool
{
  (forall j: Xid :: xUndecided(state[j]))
}

function {:inline} gConsistent(state: GState) : bool
{
  (forall j: Xid :: xConsistent(state[j]))
}

function {:inline} ExistsMonotoneExtension(snapshot: GState, state: GState, xid: Xid) : bool
{
  (exists newState: XState :: 
    state == snapshot[xid := newState] && xNoUndoneDecision(snapshot[xid], newState))
}

function {:inline} VotesEqCoordinatorState(votes: [Xid]int, state: GState, xid: Xid) : bool
{
  (votes[xid] == -1 <==> Aborted(state[xid][CoordinatorMid]))
     && (0 <= votes[xid] && votes[xid] < numParticipants
       <==> Undecided(state[xid][CoordinatorMid]))
     && (votes[xid] == numParticipants <==> Committed(state[xid][CoordinatorMid]))
}

procedure {:inline 1} GhostRead() returns (snapshot: GState);



implementation {:inline 1} GhostRead() returns (snapshot: GState)
{
  /*** structured program:
    snapshot := state;
  **** end structured program */

  anon0:
    snapshot := state;
    return;
}



function {:inline} Inv_9(state: GState, B: [Pair]bool, xid: Xid) : bool
{
  gConsistent(state)
     && (xAllParticipantsInB(xid, B) || xUndecidedOrAborted(state[xid]))
}

function {:inline} SetInv(B: [Pair]bool) : bool
{
  (forall xid: Xid, mid: Mid :: B[Pair(xid, mid)] ==> participantMid(mid))
}

function {:inline} Inv_8(state: GState, B: [Pair]bool, votes: [Xid]int) : bool
{
  gConsistent(state)
     && SetInv(B)
     && (forall xid: Xid :: VotesEqCoordinatorState(votes, state, xid))
     && (forall xid: Xid :: votes[xid] == -1 || votes[xid] == card(B, xid))
     && (forall p: Pair :: 
      B[p] && votes[xid#Pair(p)] != -1
         ==> UndecidedOrCommitted(state[xid#Pair(p)][mid#Pair(p)]))
}

function {:builtin "MapConst"} MapConstBool(bool) : [Pair]bool;

function {:builtin "MapOr"} MapOr([Pair]bool, [Pair]bool) : [Pair]bool;

function {:inline} PairCollector(x: Pair) : [Pair]bool
{
  MapConstBool(false)[x := true]
}

function {:inline} PairSetCollector(x: [Pair]bool) : [Pair]bool
{
  x
}

function card(pairs: [Pair]bool, xid: Xid) : int;

procedure Lemma_add_to_B(pair: Pair);
  requires participantMid(mid#Pair(pair));
  requires !B[pair];
  ensures (forall xid: Xid :: 
    card(B[pair := true], xid)
       == (if xid == xid#Pair(pair) then card(B, xid) + 1 else card(B, xid)));



procedure Lemma_all_in_B(xid: Xid);
  requires SetInv(B);
  ensures card(B, xid) >= numParticipants
     ==> (forall mid: Mid :: participantMid(mid) ==> B[Pair(xid, mid)]);






type {:datatype} PendingAsync;

var pendingAsyncMultiset: [PendingAsync]int;

function {:constructor} PendingAsync_Coordinator_TransactionReq() : PendingAsync;

procedure {:inline 1} AddPendingAsync_Coordinator_TransactionReq();
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_Coordinator_TransactionReq()
{

  L:
    pendingAsyncMultiset[PendingAsync_Coordinator_TransactionReq()] := pendingAsyncMultiset[PendingAsync_Coordinator_TransactionReq()] + 1;
    return;
}



function {:constructor} PendingAsync_Participant_VoteReq(xid: Xid, mid: Mid, pair: Pair) : PendingAsync;

procedure {:inline 1} AddPendingAsync_Participant_VoteReq(xid: Xid, mid: Mid, pair: Pair);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_Participant_VoteReq(xid: Xid, mid: Mid, pair: Pair)
{

  L:
    pendingAsyncMultiset[PendingAsync_Participant_VoteReq(xid, mid, pair)] := pendingAsyncMultiset[PendingAsync_Participant_VoteReq(xid, mid, pair)] + 1;
    return;
}



function {:constructor} PendingAsync_Coordinator_VoteYes(xid: Xid, mid: Mid, pair: Pair) : PendingAsync;

procedure {:inline 1} AddPendingAsync_Coordinator_VoteYes(xid: Xid, mid: Mid, pair: Pair);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_Coordinator_VoteYes(xid: Xid, mid: Mid, pair: Pair)
{

  L:
    pendingAsyncMultiset[PendingAsync_Coordinator_VoteYes(xid, mid, pair)] := pendingAsyncMultiset[PendingAsync_Coordinator_VoteYes(xid, mid, pair)] + 1;
    return;
}



function {:constructor} PendingAsync_Coordinator_VoteNo(xid: Xid, mid: Mid, pair: Pair) : PendingAsync;

procedure {:inline 1} AddPendingAsync_Coordinator_VoteNo(xid: Xid, mid: Mid, pair: Pair);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_Coordinator_VoteNo(xid: Xid, mid: Mid, pair: Pair)
{

  L:
    pendingAsyncMultiset[PendingAsync_Coordinator_VoteNo(xid, mid, pair)] := pendingAsyncMultiset[PendingAsync_Coordinator_VoteNo(xid, mid, pair)] + 1;
    return;
}



function {:constructor} PendingAsync_SetParticipantAborted(xid: Xid, mid: Mid, pair: Pair) : PendingAsync;

procedure {:inline 1} AddPendingAsync_SetParticipantAborted(xid: Xid, mid: Mid, pair: Pair);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_SetParticipantAborted(xid: Xid, mid: Mid, pair: Pair)
{

  L:
    pendingAsyncMultiset[PendingAsync_SetParticipantAborted(xid, mid, pair)] := pendingAsyncMultiset[PendingAsync_SetParticipantAborted(xid, mid, pair)] + 1;
    return;
}



function {:constructor} PendingAsync_StateUpdateOnVoteYes(xid: Xid, mid: Mid) : PendingAsync;

procedure {:inline 1} AddPendingAsync_StateUpdateOnVoteYes(xid: Xid, mid: Mid);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_StateUpdateOnVoteYes(xid: Xid, mid: Mid)
{

  L:
    pendingAsyncMultiset[PendingAsync_StateUpdateOnVoteYes(xid, mid)] := pendingAsyncMultiset[PendingAsync_StateUpdateOnVoteYes(xid, mid)] + 1;
    return;
}



function {:constructor} PendingAsync_StateUpdateOnVoteNo(xid: Xid, mid: Mid) : PendingAsync;

procedure {:inline 1} AddPendingAsync_StateUpdateOnVoteNo(xid: Xid, mid: Mid);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_StateUpdateOnVoteNo(xid: Xid, mid: Mid)
{

  L:
    pendingAsyncMultiset[PendingAsync_StateUpdateOnVoteNo(xid, mid)] := pendingAsyncMultiset[PendingAsync_StateUpdateOnVoteNo(xid, mid)] + 1;
    return;
}



function {:constructor} PendingAsync_Participant_Commit(xid: Xid, mid: Mid) : PendingAsync;

procedure {:inline 1} AddPendingAsync_Participant_Commit(xid: Xid, mid: Mid);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_Participant_Commit(xid: Xid, mid: Mid)
{

  L:
    pendingAsyncMultiset[PendingAsync_Participant_Commit(xid, mid)] := pendingAsyncMultiset[PendingAsync_Participant_Commit(xid, mid)] + 1;
    return;
}



function {:constructor} PendingAsync_Participant_Abort(xid: Xid, mid: Mid) : PendingAsync;

procedure {:inline 1} AddPendingAsync_Participant_Abort(xid: Xid, mid: Mid);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_Participant_Abort(xid: Xid, mid: Mid)
{

  L:
    pendingAsyncMultiset[PendingAsync_Participant_Abort(xid, mid)] := pendingAsyncMultiset[PendingAsync_Participant_Abort(xid, mid)] + 1;
    return;
}



function {:constructor} PendingAsync_AllocateXid() : PendingAsync;

procedure {:inline 1} AddPendingAsync_AllocateXid();
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_AllocateXid()
{

  L:
    pendingAsyncMultiset[PendingAsync_AllocateXid()] := pendingAsyncMultiset[PendingAsync_AllocateXid()] + 1;
    return;
}



function {:constructor} PendingAsync_TransferPair(xid: Xid, mid: Mid, inPairs: [Pair]bool) : PendingAsync;

procedure {:inline 1} AddPendingAsync_TransferPair(xid: Xid, mid: Mid, inPairs: [Pair]bool);
  modifies pendingAsyncMultiset;



implementation {:inline 1} AddPendingAsync_TransferPair(xid: Xid, mid: Mid, inPairs: [Pair]bool)
{

  L:
    pendingAsyncMultiset[PendingAsync_TransferPair(xid, mid, inPairs)] := pendingAsyncMultiset[PendingAsync_TransferPair(xid, mid, inPairs)] + 1;
    return;
}



procedure {:inline 1} atomic_SetParticipantAborted_8(xid: Xid, mid: Mid, pair: Pair);
  free requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  modifies state;



procedure {:inline 1} atomic_StateUpdateOnVoteYes_8(xid: Xid, mid: Mid) returns (commit: bool);
  modifies votes, state, B;



procedure {:inline 1} atomic_StateUpdateOnVoteNo_8(xid: Xid, mid: Mid) returns (abort: bool);
  modifies votes, state;



procedure {:inline 1} atomic_Participant_Commit_8(xid: Xid, mid: Mid);
  modifies state;



procedure {:inline 1} atomic_Participant_Abort_8(xid: Xid, mid: Mid);
  modifies state;



procedure {:inline 1} atomic_AllocateXid_8() returns (xid: Xid, pairs: [Pair]bool);
  modifies AllocatedXids;
  free ensures (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairSetCollector(pairs), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));



procedure {:inline 1} atomic_TransferPair_8(xid: Xid, mid: Mid, inPairs: [Pair]bool) returns (pairs: [Pair]bool, pair: Pair);
  free requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairSetCollector(inPairs), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  free ensures (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairSetCollector(pairs), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
         == linear_pair_MapConstBool(true));



implementation {:inline 1} atomic_SetParticipantAborted_8(xid: Xid, mid: Mid, pair: Pair)
{
  /*** structured program:
    assert pair(xid, mid, pair);
    assert xUndecidedOrAborted(state[xid]);
    state[xid][mid] := ABORTED();
  **** end structured program */

  anon0:
    state[xid][mid] := ABORTED();
    return;
}



implementation {:inline 1} atomic_StateUpdateOnVoteYes_8(xid: Xid, mid: Mid) returns (commit: bool)
{
  /*** structured program:
    assert AllocatedXids[xid];
    assert VotesEqCoordinatorState(votes, state, xid);
    B[Pair(xid, mid)] := true;
    if (votes[xid] == -1)
    {
        commit := false;
    }
    else
    {
        votes[xid] := votes[xid] + 1;
        commit := votes[xid] == numParticipants;
        state[xid][CoordinatorMid] := (if commit then COMMITTED() else state[xid][CoordinatorMid]);
    }
  **** end structured program */

  anon0:
    B[Pair(xid, mid)] := true;
    goto anon3_Then, anon3_Else;

  anon3_Else:
    assume {:partition} votes[xid] != -1;
    votes[xid] := votes[xid] + 1;
    commit := votes[xid] == numParticipants;
    state[xid][CoordinatorMid] := (if commit then COMMITTED() else state[xid][CoordinatorMid]);
    return;

  anon3_Then:
    assume {:partition} votes[xid] == -1;
    commit := false;
    return;
}



implementation {:inline 1} atomic_StateUpdateOnVoteNo_8(xid: Xid, mid: Mid) returns (abort: bool)
{
  /*** structured program:
    assert AllocatedXids[xid];
    assert !Committed(state[xid][CoordinatorMid]);
    abort := votes[xid] != -1;
    votes[xid] := -1;
    state[xid][CoordinatorMid] := (if abort then ABORTED() else state[xid][CoordinatorMid]);
  **** end structured program */

  anon0:
    abort := votes[xid] != -1;
    votes[xid] := -1;
    state[xid][CoordinatorMid] := (if abort then ABORTED() else state[xid][CoordinatorMid]);
    return;
}



implementation {:inline 1} atomic_Participant_Commit_8(xid: Xid, mid: Mid)
{
  /*** structured program:
    assert participantMid(mid);
    assert xUndecidedOrCommitted(state[xid]);
    assert Committed(state[xid][CoordinatorMid]);
    state[xid][mid] := COMMITTED();
  **** end structured program */

  anon0:
    state[xid][mid] := COMMITTED();
    return;
}



implementation {:inline 1} atomic_Participant_Abort_8(xid: Xid, mid: Mid)
{
  /*** structured program:
    assert participantMid(mid);
    assert xUndecidedOrAborted(state[xid]);
    assert Aborted(state[xid][CoordinatorMid]);
    state[xid][mid] := ABORTED();
  **** end structured program */

  anon0:
    state[xid][mid] := ABORTED();
    return;
}



implementation {:inline 1} atomic_AllocateXid_8() returns (xid: Xid, pairs: [Pair]bool)
{
  /*** structured program:
    assume !AllocatedXids[xid];
    assume state[xid] == (lambda j: Mid :: UNDECIDED());
    pairs := (lambda p: Pair :: pair(xid, mid#Pair(p), p));
    AllocatedXids[xid] := true;
  **** end structured program */

  anon0:
    assume !AllocatedXids[xid];
    assume state[xid] == (lambda j: Mid :: UNDECIDED());
    pairs := (lambda p: Pair :: pair(xid, mid#Pair(p), p));
    AllocatedXids[xid] := true;
    return;
}



implementation {:inline 1} atomic_TransferPair_8(xid: Xid, mid: Mid, inPairs: [Pair]bool) returns (pairs: [Pair]bool, pair: Pair)
{
  /*** structured program:
    pair := Pair(xid, mid);
    pairs := inPairs[pair := false];
  **** end structured program */

  anon0:
    pair := Pair(xid, mid);
    pairs := inPairs[pair := false];
    return;
}



procedure {:inline 1} atomic_Coordinator_VoteYes_9(xid: Xid, mid: Mid, pair: Pair);
  free requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  modifies state, B;



procedure {:inline 1} atomic_Coordinator_VoteNo_9(xid: Xid, mid: Mid, pair: Pair);
  free requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  modifies state;



procedure {:inline 1} atomic_SetParticipantAborted_9(xid: Xid, mid: Mid, pair: Pair);
  free requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  modifies state;



procedure {:inline 1} atomic_AllocateXid_9() returns (xid: Xid, pairs: [Pair]bool);
  modifies AllocatedXids;
  free ensures (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairSetCollector(pairs), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));



procedure {:inline 1} atomic_TransferPair_9(xid: Xid, mid: Mid, inPairs: [Pair]bool) returns (pairs: [Pair]bool, pair: Pair);
  free requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairSetCollector(inPairs), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  free ensures (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairSetCollector(pairs), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
         == linear_pair_MapConstBool(true));



implementation {:inline 1} atomic_Coordinator_VoteYes_9(xid: Xid, mid: Mid, pair: Pair)
{
  var oldState: XState;
  var newState: XState;

  /*** structured program:
    assert AllocatedXids[xid];
    assert pair(xid, mid, pair);
    assert xConsistent(state[xid]);
    B[pair] := true;
    oldState := state[xid];
    if (*)
    {
        assume xAllParticipantsInB(xid, B);
        assume xConsistentExtension(oldState, newState);
        state[xid] := newState;
    }
  **** end structured program */

  anon0:
    B[pair] := true;
    oldState := state[xid];
    goto anon2_Then, anon2_Else;

  anon2_Else:
    return;

  anon2_Then:
    assume xAllParticipantsInB(xid, B);
    assume xConsistentExtension(oldState, newState);
    state[xid] := newState;
    return;
}



implementation {:inline 1} atomic_Coordinator_VoteNo_9(xid: Xid, mid: Mid, pair: Pair)
{
  var oldState: XState;
  var newState: XState;

  /*** structured program:
    assert AllocatedXids[xid];
    assert pair(xid, mid, pair);
    assert xUndecidedOrAborted(state[xid]);
    oldState := state[xid];
    assume xUndecidedOrAborted(newState);
    assume xConsistentExtension(oldState, newState);
    state[xid] := newState;
  **** end structured program */

  anon0:
    oldState := state[xid];
    assume xUndecidedOrAborted(newState);
    assume xConsistentExtension(oldState, newState);
    state[xid] := newState;
    return;
}



implementation {:inline 1} atomic_SetParticipantAborted_9(xid: Xid, mid: Mid, pair: Pair)
{
  /*** structured program:
    assert pair(xid, mid, pair);
    assert xUndecidedOrAborted(state[xid]);
    state[xid][mid] := ABORTED();
  **** end structured program */

  anon0:
    state[xid][mid] := ABORTED();
    return;
}



implementation {:inline 1} atomic_AllocateXid_9() returns (xid: Xid, pairs: [Pair]bool)
{
  /*** structured program:
    assume !AllocatedXids[xid];
    assume state[xid] == (lambda j: Mid :: UNDECIDED());
    pairs := (lambda p: Pair :: pair(xid, mid#Pair(p), p));
    AllocatedXids[xid] := true;
  **** end structured program */

  anon0:
    assume !AllocatedXids[xid];
    assume state[xid] == (lambda j: Mid :: UNDECIDED());
    pairs := (lambda p: Pair :: pair(xid, mid#Pair(p), p));
    AllocatedXids[xid] := true;
    return;
}



implementation {:inline 1} atomic_TransferPair_9(xid: Xid, mid: Mid, inPairs: [Pair]bool) returns (pairs: [Pair]bool, pair: Pair)
{
  /*** structured program:
    pair := Pair(xid, mid);
    pairs := inPairs[pair := false];
  **** end structured program */

  anon0:
    pair := Pair(xid, mid);
    pairs := inPairs[pair := false];
    return;
}



procedure {:inline 1} atomic_Participant_VoteReq_10(xid: Xid, mid: Mid, pair: Pair);
  free requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  modifies state;



procedure {:inline 1} atomic_AllocateXid_10() returns (xid: Xid, pairs: [Pair]bool);
  modifies AllocatedXids;
  free ensures (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairSetCollector(pairs), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));



procedure {:inline 1} atomic_TransferPair_10(xid: Xid, mid: Mid, inPairs: [Pair]bool) returns (pairs: [Pair]bool, pair: Pair);
  free requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairSetCollector(inPairs), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  free ensures (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairSetCollector(pairs), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
         == linear_pair_MapConstBool(true));



implementation {:inline 1} atomic_Participant_VoteReq_10(xid: Xid, mid: Mid, pair: Pair)
{
  var oldState: XState;
  var newState: XState;

  /*** structured program:
    assert AllocatedXids[xid];
    assert pair(xid, mid, pair);
    assert xConsistent(state[xid]);
    oldState := state[xid];
    assume xConsistentExtension(oldState, newState);
    state[xid] := newState;
  **** end structured program */

  anon0:
    oldState := state[xid];
    assume xConsistentExtension(oldState, newState);
    state[xid] := newState;
    return;
}



implementation {:inline 1} atomic_AllocateXid_10() returns (xid: Xid, pairs: [Pair]bool)
{
  /*** structured program:
    assume !AllocatedXids[xid];
    assume state[xid] == (lambda j: Mid :: UNDECIDED());
    pairs := (lambda p: Pair :: pair(xid, mid#Pair(p), p));
    AllocatedXids[xid] := true;
  **** end structured program */

  anon0:
    assume !AllocatedXids[xid];
    assume state[xid] == (lambda j: Mid :: UNDECIDED());
    pairs := (lambda p: Pair :: pair(xid, mid#Pair(p), p));
    AllocatedXids[xid] := true;
    return;
}



implementation {:inline 1} atomic_TransferPair_10(xid: Xid, mid: Mid, inPairs: [Pair]bool) returns (pairs: [Pair]bool, pair: Pair)
{
  /*** structured program:
    pair := Pair(xid, mid);
    pairs := inPairs[pair := false];
  **** end structured program */

  anon0:
    pair := Pair(xid, mid);
    pairs := inPairs[pair := false];
    return;
}



procedure {:inline 1} atomic_Coordinator_TransactionReq_11() returns (xid: Xid);
  modifies state;



implementation {:inline 1} atomic_Coordinator_TransactionReq_11() returns (xid: Xid)
{
  var newState: XState;

  /*** structured program:
    assume xConsistent(newState);
    state[xid] := newState;
  **** end structured program */

  anon0:
    assume xConsistent(newState);
    state[xid] := newState;
    return;
}



var linear_pair_hole: [Pair]bool;

function linear_pair_MapConstBool(b: bool) : [Pair]bool;

function linear_pair_MapConstInt(b: int) : [Pair]int;

function linear_pair_MapEq(a: [Pair]int, b: [Pair]int) : [Pair]bool;

function linear_pair_MapImp(a: [Pair]bool, b: [Pair]bool) : [Pair]bool;

function linear_pair_MapOr(a: [Pair]bool, b: [Pair]bool) : [Pair]bool;

axiom (forall a: [Pair]bool, b: [Pair]bool :: 
  { linear_pair_MapOr(a, b) } 
  (forall x: Pair :: linear_pair_MapOr(a, b)[x] <==> a[x] || b[x]));

axiom (forall a: [Pair]bool, b: [Pair]bool :: 
  { linear_pair_MapImp(a, b) } 
  (forall x: Pair :: linear_pair_MapImp(a, b)[x] <==> a[x] ==> b[x]));

axiom (forall x: Pair :: linear_pair_MapConstBool(true)[x]);

axiom (forall x: Pair :: !linear_pair_MapConstBool(false)[x]);

axiom (forall a: [Pair]int, b: [Pair]int :: 
  { linear_pair_MapEq(a, b) } 
  (forall x: Pair :: linear_pair_MapEq(a, b)[x] <==> a[x] == b[x]));

axiom (forall a: int, x: Pair :: linear_pair_MapConstInt(a)[x] == a);

implementation CommutativityChecker_atomic_SetParticipantAborted_8_atomic_Participant_Commit_8(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid)
{

  first_anon0:
    state[first_xid][first_mid] := ABORTED();
    goto second_anon0;

  second_anon0:
    state[second_xid][second_mid] := COMMITTED();
    return;
}



procedure CommutativityChecker_atomic_SetParticipantAborted_8_atomic_Participant_Commit_8(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid);
  requires true;
  requires pair(first_xid, first_mid, first_pair);
  requires xUndecidedOrAborted(state[first_xid]);
  requires participantMid(second_mid);
  requires xUndecidedOrCommitted(state[second_xid]);
  requires Committed(state[second_xid][CoordinatorMid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> state
       == old(state)[second_xid := old(state)[second_xid][second_mid := COMMITTED()]][first_xid := old(state)[second_xid := old(state)[second_xid][second_mid := COMMITTED()]][first_xid][first_mid := ABORTED()]];



implementation GatePreservationChecker_atomic_Participant_Commit_8_atomic_SetParticipantAborted_8(first_xid: Xid, 
    first_mid: Mid, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair)
{

  second_anon0:
    state[second_xid][second_mid] := ABORTED();
    return;
}



procedure GatePreservationChecker_atomic_Participant_Commit_8_atomic_SetParticipantAborted_8(first_xid: Xid, 
    first_mid: Mid, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair);
  requires true;
  requires pair(second_xid, second_mid, second_pair);
  requires xUndecidedOrAborted(state[second_xid]);
  requires participantMid(first_mid);
  requires xUndecidedOrCommitted(state[first_xid]);
  requires Committed(state[first_xid][CoordinatorMid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true ==> participantMid(first_mid);
  ensures true ==> xUndecidedOrCommitted(state[first_xid]);
  ensures true ==> Committed(state[first_xid][CoordinatorMid]);



implementation FailurePreservationChecker_atomic_SetParticipantAborted_8_atomic_Participant_Commit_8(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid)
{

  second_anon0:
    state[second_xid][second_mid] := COMMITTED();
    return;
}



procedure FailurePreservationChecker_atomic_SetParticipantAborted_8_atomic_Participant_Commit_8(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid);
  requires true;
  requires !(pair(first_xid, first_mid, first_pair)
     && xUndecidedOrAborted(state[first_xid]));
  requires participantMid(second_mid);
  requires xUndecidedOrCommitted(state[second_xid]);
  requires Committed(state[second_xid][CoordinatorMid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> !(pair(first_xid, first_mid, first_pair)
       && xUndecidedOrAborted(state[first_xid]));



implementation CommutativityChecker_atomic_StateUpdateOnVoteYes_8_atomic_Participant_Commit_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
   returns (first_commit: bool)
{

  first_anon0:
    B[Pair(first_xid, first_mid)] := true;
    goto first_anon3_Then, first_anon3_Else;

  first_anon3_Else:
    assume {:partition} votes[first_xid] != -1;
    votes[first_xid] := votes[first_xid] + 1;
    first_commit := votes[first_xid] == numParticipants;
    state[first_xid][CoordinatorMid] := (if first_commit then COMMITTED() else state[first_xid][CoordinatorMid]);
    goto second_anon0;

  first_anon3_Then:
    assume {:partition} votes[first_xid] == -1;
    first_commit := false;
    goto second_anon0;

  second_anon0:
    state[second_xid][second_mid] := COMMITTED();
    return;
}



procedure CommutativityChecker_atomic_StateUpdateOnVoteYes_8_atomic_Participant_Commit_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
   returns (first_commit: bool);
  requires true;
  requires AllocatedXids[first_xid];
  requires VotesEqCoordinatorState(votes, state, first_xid);
  requires participantMid(second_mid);
  requires xUndecidedOrCommitted(state[second_xid]);
  requires Committed(state[second_xid][CoordinatorMid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> (
        AllocatedXids == old(AllocatedXids)
         && votes == old(votes)
         && state
           == old(state)[second_xid := old(state)[second_xid][second_mid := COMMITTED()]]
         && B == old(B)[Pair(first_xid, first_mid) := true]
         && (first_commit <==> false)
         && old(votes)[first_xid] == -1)
       || (
        AllocatedXids == old(AllocatedXids)
         && votes == old(votes)[first_xid := old(votes)[first_xid] + 1]
         && state
           == old(state)[second_xid := old(state)[second_xid][second_mid := COMMITTED()]][first_xid := old(state)[second_xid := old(state)[second_xid][second_mid := COMMITTED()]][first_xid][CoordinatorMid := (if old(votes)[first_xid := old(votes)[first_xid] + 1][first_xid] == numParticipants
             then COMMITTED()
             else old(state)[second_xid := old(state)[second_xid][second_mid := COMMITTED()]][first_xid][CoordinatorMid])]]
         && B == old(B)[Pair(first_xid, first_mid) := true]
         && (first_commit
           <==> old(votes)[first_xid := old(votes)[first_xid] + 1][first_xid] == numParticipants)
         && old(votes)[first_xid] != -1);



implementation GatePreservationChecker_atomic_Participant_Commit_8_atomic_StateUpdateOnVoteYes_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
   returns (second_commit: bool)
{

  second_anon0:
    B[Pair(second_xid, second_mid)] := true;
    goto second_anon3_Then, second_anon3_Else;

  second_anon3_Else:
    assume {:partition} votes[second_xid] != -1;
    votes[second_xid] := votes[second_xid] + 1;
    second_commit := votes[second_xid] == numParticipants;
    state[second_xid][CoordinatorMid] := (if second_commit then COMMITTED() else state[second_xid][CoordinatorMid]);
    return;

  second_anon3_Then:
    assume {:partition} votes[second_xid] == -1;
    second_commit := false;
    return;
}



procedure GatePreservationChecker_atomic_Participant_Commit_8_atomic_StateUpdateOnVoteYes_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
   returns (second_commit: bool);
  requires true;
  requires AllocatedXids[second_xid];
  requires VotesEqCoordinatorState(votes, state, second_xid);
  requires participantMid(first_mid);
  requires xUndecidedOrCommitted(state[first_xid]);
  requires Committed(state[first_xid][CoordinatorMid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true ==> participantMid(first_mid);
  ensures true ==> xUndecidedOrCommitted(state[first_xid]);
  ensures true ==> Committed(state[first_xid][CoordinatorMid]);



implementation FailurePreservationChecker_atomic_StateUpdateOnVoteYes_8_atomic_Participant_Commit_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
   returns (first_commit: bool)
{

  second_anon0:
    state[second_xid][second_mid] := COMMITTED();
    return;
}



procedure FailurePreservationChecker_atomic_StateUpdateOnVoteYes_8_atomic_Participant_Commit_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
   returns (first_commit: bool);
  requires true;
  requires !(AllocatedXids[first_xid] && VotesEqCoordinatorState(votes, state, first_xid));
  requires participantMid(second_mid);
  requires xUndecidedOrCommitted(state[second_xid]);
  requires Committed(state[second_xid][CoordinatorMid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> !(AllocatedXids[first_xid] && VotesEqCoordinatorState(votes, state, first_xid));



implementation CommutativityChecker_atomic_StateUpdateOnVoteNo_8_atomic_Participant_Commit_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
   returns (first_abort: bool)
{

  first_anon0:
    first_abort := votes[first_xid] != -1;
    votes[first_xid] := -1;
    state[first_xid][CoordinatorMid] := (if first_abort then ABORTED() else state[first_xid][CoordinatorMid]);
    goto second_anon0;

  second_anon0:
    state[second_xid][second_mid] := COMMITTED();
    return;
}



procedure CommutativityChecker_atomic_StateUpdateOnVoteNo_8_atomic_Participant_Commit_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
   returns (first_abort: bool);
  requires true;
  requires AllocatedXids[first_xid];
  requires !Committed(state[first_xid][CoordinatorMid]);
  requires participantMid(second_mid);
  requires xUndecidedOrCommitted(state[second_xid]);
  requires Committed(state[second_xid][CoordinatorMid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> AllocatedXids == old(AllocatedXids)
       && state
         == old(state)[second_xid := old(state)[second_xid][second_mid := COMMITTED()]][first_xid := old(state)[second_xid := old(state)[second_xid][second_mid := COMMITTED()]][first_xid][CoordinatorMid := (if old(votes)[first_xid] != -1
           then ABORTED()
           else old(state)[second_xid := old(state)[second_xid][second_mid := COMMITTED()]][first_xid][CoordinatorMid])]]
       && votes == old(votes)[first_xid := -1]
       && (first_abort <==> old(votes)[first_xid] != -1);



implementation GatePreservationChecker_atomic_Participant_Commit_8_atomic_StateUpdateOnVoteNo_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
   returns (second_abort: bool)
{

  second_anon0:
    second_abort := votes[second_xid] != -1;
    votes[second_xid] := -1;
    state[second_xid][CoordinatorMid] := (if second_abort then ABORTED() else state[second_xid][CoordinatorMid]);
    return;
}



procedure GatePreservationChecker_atomic_Participant_Commit_8_atomic_StateUpdateOnVoteNo_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
   returns (second_abort: bool);
  requires true;
  requires AllocatedXids[second_xid];
  requires !Committed(state[second_xid][CoordinatorMid]);
  requires participantMid(first_mid);
  requires xUndecidedOrCommitted(state[first_xid]);
  requires Committed(state[first_xid][CoordinatorMid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true ==> participantMid(first_mid);
  ensures true ==> xUndecidedOrCommitted(state[first_xid]);
  ensures true ==> Committed(state[first_xid][CoordinatorMid]);



implementation FailurePreservationChecker_atomic_StateUpdateOnVoteNo_8_atomic_Participant_Commit_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
   returns (first_abort: bool)
{

  second_anon0:
    state[second_xid][second_mid] := COMMITTED();
    return;
}



procedure FailurePreservationChecker_atomic_StateUpdateOnVoteNo_8_atomic_Participant_Commit_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
   returns (first_abort: bool);
  requires true;
  requires !(AllocatedXids[first_xid] && !Committed(state[first_xid][CoordinatorMid]));
  requires participantMid(second_mid);
  requires xUndecidedOrCommitted(state[second_xid]);
  requires Committed(state[second_xid][CoordinatorMid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> !(AllocatedXids[first_xid] && !Committed(state[first_xid][CoordinatorMid]));



implementation CommutativityChecker_atomic_Participant_Commit_8_atomic_Participant_Commit_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
{

  first_anon0:
    state[first_xid][first_mid] := COMMITTED();
    goto second_anon0;

  second_anon0:
    state[second_xid][second_mid] := COMMITTED();
    return;
}



procedure CommutativityChecker_atomic_Participant_Commit_8_atomic_Participant_Commit_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid);
  requires true;
  requires participantMid(first_mid);
  requires xUndecidedOrCommitted(state[first_xid]);
  requires Committed(state[first_xid][CoordinatorMid]);
  requires participantMid(second_mid);
  requires xUndecidedOrCommitted(state[second_xid]);
  requires Committed(state[second_xid][CoordinatorMid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> state
       == old(state)[second_xid := old(state)[second_xid][second_mid := COMMITTED()]][first_xid := old(state)[second_xid := old(state)[second_xid][second_mid := COMMITTED()]][first_xid][first_mid := COMMITTED()]];



implementation GatePreservationChecker_atomic_Participant_Commit_8_atomic_Participant_Commit_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
{

  second_anon0:
    state[second_xid][second_mid] := COMMITTED();
    return;
}



procedure GatePreservationChecker_atomic_Participant_Commit_8_atomic_Participant_Commit_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid);
  requires true;
  requires participantMid(second_mid);
  requires xUndecidedOrCommitted(state[second_xid]);
  requires Committed(state[second_xid][CoordinatorMid]);
  requires participantMid(first_mid);
  requires xUndecidedOrCommitted(state[first_xid]);
  requires Committed(state[first_xid][CoordinatorMid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true ==> participantMid(first_mid);
  ensures true ==> xUndecidedOrCommitted(state[first_xid]);
  ensures true ==> Committed(state[first_xid][CoordinatorMid]);



implementation FailurePreservationChecker_atomic_Participant_Commit_8_atomic_Participant_Commit_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
{

  second_anon0:
    state[second_xid][second_mid] := COMMITTED();
    return;
}



procedure FailurePreservationChecker_atomic_Participant_Commit_8_atomic_Participant_Commit_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid);
  requires true;
  requires !(
    participantMid(first_mid)
     && xUndecidedOrCommitted(state[first_xid])
     && Committed(state[first_xid][CoordinatorMid]));
  requires participantMid(second_mid);
  requires xUndecidedOrCommitted(state[second_xid]);
  requires Committed(state[second_xid][CoordinatorMid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> !(
      participantMid(first_mid)
       && xUndecidedOrCommitted(state[first_xid])
       && Committed(state[first_xid][CoordinatorMid]));



implementation CommutativityChecker_atomic_Participant_Abort_8_atomic_Participant_Commit_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
{

  first_anon0:
    state[first_xid][first_mid] := ABORTED();
    goto second_anon0;

  second_anon0:
    state[second_xid][second_mid] := COMMITTED();
    return;
}



procedure CommutativityChecker_atomic_Participant_Abort_8_atomic_Participant_Commit_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid);
  requires true;
  requires participantMid(first_mid);
  requires xUndecidedOrAborted(state[first_xid]);
  requires Aborted(state[first_xid][CoordinatorMid]);
  requires participantMid(second_mid);
  requires xUndecidedOrCommitted(state[second_xid]);
  requires Committed(state[second_xid][CoordinatorMid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> state
       == old(state)[second_xid := old(state)[second_xid][second_mid := COMMITTED()]][first_xid := old(state)[second_xid := old(state)[second_xid][second_mid := COMMITTED()]][first_xid][first_mid := ABORTED()]];



implementation GatePreservationChecker_atomic_Participant_Commit_8_atomic_Participant_Abort_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
{

  second_anon0:
    state[second_xid][second_mid] := ABORTED();
    return;
}



procedure GatePreservationChecker_atomic_Participant_Commit_8_atomic_Participant_Abort_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid);
  requires true;
  requires participantMid(second_mid);
  requires xUndecidedOrAborted(state[second_xid]);
  requires Aborted(state[second_xid][CoordinatorMid]);
  requires participantMid(first_mid);
  requires xUndecidedOrCommitted(state[first_xid]);
  requires Committed(state[first_xid][CoordinatorMid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true ==> participantMid(first_mid);
  ensures true ==> xUndecidedOrCommitted(state[first_xid]);
  ensures true ==> Committed(state[first_xid][CoordinatorMid]);



implementation FailurePreservationChecker_atomic_Participant_Abort_8_atomic_Participant_Commit_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
{

  second_anon0:
    state[second_xid][second_mid] := COMMITTED();
    return;
}



procedure FailurePreservationChecker_atomic_Participant_Abort_8_atomic_Participant_Commit_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid);
  requires true;
  requires !(
    participantMid(first_mid)
     && xUndecidedOrAborted(state[first_xid])
     && Aborted(state[first_xid][CoordinatorMid]));
  requires participantMid(second_mid);
  requires xUndecidedOrCommitted(state[second_xid]);
  requires Committed(state[second_xid][CoordinatorMid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> !(
      participantMid(first_mid)
       && xUndecidedOrAborted(state[first_xid])
       && Aborted(state[first_xid][CoordinatorMid]));



implementation CommutativityChecker_atomic_AllocateXid_8_atomic_Participant_Commit_8(second_xid: Xid, second_mid: Mid)
   returns (first_xid: Xid, first_pairs: [Pair]bool)
{

  first_anon0:
    assume !AllocatedXids[first_xid];
    assume state[first_xid] == (lambda first_j: Mid :: UNDECIDED());
    first_pairs := (lambda first_p: Pair :: pair(first_xid, mid#Pair(first_p), first_p));
    AllocatedXids[first_xid] := true;
    goto second_anon0;

  second_anon0:
    state[second_xid][second_mid] := COMMITTED();
    return;
}



procedure CommutativityChecker_atomic_AllocateXid_8_atomic_Participant_Commit_8(second_xid: Xid, second_mid: Mid)
   returns (first_xid: Xid, first_pairs: [Pair]bool);
  requires true;
  requires participantMid(second_mid);
  requires xUndecidedOrCommitted(state[second_xid]);
  requires Committed(state[second_xid][CoordinatorMid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> AllocatedXids == old(AllocatedXids)[first_xid := true]
       && state
         == old(state)[second_xid := old(state)[second_xid][second_mid := COMMITTED()]]
       && first_xid == first_xid
       && first_pairs
         == (lambda first_p: Pair :: pair(first_xid, mid#Pair(first_p), first_p))
       && old(state)[second_xid := old(state)[second_xid][second_mid := COMMITTED()]][first_xid]
         == (lambda first_j: Mid :: UNDECIDED())
       && !old(AllocatedXids)[first_xid];



implementation CommutativityChecker_atomic_SetParticipantAborted_8_atomic_Participant_Abort_8(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid)
{

  first_anon0:
    state[first_xid][first_mid] := ABORTED();
    goto second_anon0;

  second_anon0:
    state[second_xid][second_mid] := ABORTED();
    return;
}



procedure CommutativityChecker_atomic_SetParticipantAborted_8_atomic_Participant_Abort_8(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid);
  requires true;
  requires pair(first_xid, first_mid, first_pair);
  requires xUndecidedOrAborted(state[first_xid]);
  requires participantMid(second_mid);
  requires xUndecidedOrAborted(state[second_xid]);
  requires Aborted(state[second_xid][CoordinatorMid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> state
       == old(state)[second_xid := old(state)[second_xid][second_mid := ABORTED()]][first_xid := old(state)[second_xid := old(state)[second_xid][second_mid := ABORTED()]][first_xid][first_mid := ABORTED()]];



implementation GatePreservationChecker_atomic_Participant_Abort_8_atomic_SetParticipantAborted_8(first_xid: Xid, 
    first_mid: Mid, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair)
{

  second_anon0:
    state[second_xid][second_mid] := ABORTED();
    return;
}



procedure GatePreservationChecker_atomic_Participant_Abort_8_atomic_SetParticipantAborted_8(first_xid: Xid, 
    first_mid: Mid, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair);
  requires true;
  requires pair(second_xid, second_mid, second_pair);
  requires xUndecidedOrAborted(state[second_xid]);
  requires participantMid(first_mid);
  requires xUndecidedOrAborted(state[first_xid]);
  requires Aborted(state[first_xid][CoordinatorMid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true ==> participantMid(first_mid);
  ensures true ==> xUndecidedOrAborted(state[first_xid]);
  ensures true ==> Aborted(state[first_xid][CoordinatorMid]);



implementation FailurePreservationChecker_atomic_SetParticipantAborted_8_atomic_Participant_Abort_8(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid)
{

  second_anon0:
    state[second_xid][second_mid] := ABORTED();
    return;
}



procedure FailurePreservationChecker_atomic_SetParticipantAborted_8_atomic_Participant_Abort_8(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid);
  requires true;
  requires !(pair(first_xid, first_mid, first_pair)
     && xUndecidedOrAborted(state[first_xid]));
  requires participantMid(second_mid);
  requires xUndecidedOrAborted(state[second_xid]);
  requires Aborted(state[second_xid][CoordinatorMid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> !(pair(first_xid, first_mid, first_pair)
       && xUndecidedOrAborted(state[first_xid]));



implementation CommutativityChecker_atomic_StateUpdateOnVoteYes_8_atomic_Participant_Abort_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
   returns (first_commit: bool)
{

  first_anon0:
    B[Pair(first_xid, first_mid)] := true;
    goto first_anon3_Then, first_anon3_Else;

  first_anon3_Else:
    assume {:partition} votes[first_xid] != -1;
    votes[first_xid] := votes[first_xid] + 1;
    first_commit := votes[first_xid] == numParticipants;
    state[first_xid][CoordinatorMid] := (if first_commit then COMMITTED() else state[first_xid][CoordinatorMid]);
    goto second_anon0;

  first_anon3_Then:
    assume {:partition} votes[first_xid] == -1;
    first_commit := false;
    goto second_anon0;

  second_anon0:
    state[second_xid][second_mid] := ABORTED();
    return;
}



procedure CommutativityChecker_atomic_StateUpdateOnVoteYes_8_atomic_Participant_Abort_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
   returns (first_commit: bool);
  requires true;
  requires AllocatedXids[first_xid];
  requires VotesEqCoordinatorState(votes, state, first_xid);
  requires participantMid(second_mid);
  requires xUndecidedOrAborted(state[second_xid]);
  requires Aborted(state[second_xid][CoordinatorMid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> (
        AllocatedXids == old(AllocatedXids)
         && votes == old(votes)
         && state
           == old(state)[second_xid := old(state)[second_xid][second_mid := ABORTED()]]
         && B == old(B)[Pair(first_xid, first_mid) := true]
         && (first_commit <==> false)
         && old(votes)[first_xid] == -1)
       || (
        AllocatedXids == old(AllocatedXids)
         && votes == old(votes)[first_xid := old(votes)[first_xid] + 1]
         && state
           == old(state)[second_xid := old(state)[second_xid][second_mid := ABORTED()]][first_xid := old(state)[second_xid := old(state)[second_xid][second_mid := ABORTED()]][first_xid][CoordinatorMid := (if old(votes)[first_xid := old(votes)[first_xid] + 1][first_xid] == numParticipants
             then COMMITTED()
             else old(state)[second_xid := old(state)[second_xid][second_mid := ABORTED()]][first_xid][CoordinatorMid])]]
         && B == old(B)[Pair(first_xid, first_mid) := true]
         && (first_commit
           <==> old(votes)[first_xid := old(votes)[first_xid] + 1][first_xid] == numParticipants)
         && old(votes)[first_xid] != -1);



implementation GatePreservationChecker_atomic_Participant_Abort_8_atomic_StateUpdateOnVoteYes_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
   returns (second_commit: bool)
{

  second_anon0:
    B[Pair(second_xid, second_mid)] := true;
    goto second_anon3_Then, second_anon3_Else;

  second_anon3_Else:
    assume {:partition} votes[second_xid] != -1;
    votes[second_xid] := votes[second_xid] + 1;
    second_commit := votes[second_xid] == numParticipants;
    state[second_xid][CoordinatorMid] := (if second_commit then COMMITTED() else state[second_xid][CoordinatorMid]);
    return;

  second_anon3_Then:
    assume {:partition} votes[second_xid] == -1;
    second_commit := false;
    return;
}



procedure GatePreservationChecker_atomic_Participant_Abort_8_atomic_StateUpdateOnVoteYes_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
   returns (second_commit: bool);
  requires true;
  requires AllocatedXids[second_xid];
  requires VotesEqCoordinatorState(votes, state, second_xid);
  requires participantMid(first_mid);
  requires xUndecidedOrAborted(state[first_xid]);
  requires Aborted(state[first_xid][CoordinatorMid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true ==> participantMid(first_mid);
  ensures true ==> xUndecidedOrAborted(state[first_xid]);
  ensures true ==> Aborted(state[first_xid][CoordinatorMid]);



implementation FailurePreservationChecker_atomic_StateUpdateOnVoteYes_8_atomic_Participant_Abort_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
   returns (first_commit: bool)
{

  second_anon0:
    state[second_xid][second_mid] := ABORTED();
    return;
}



procedure FailurePreservationChecker_atomic_StateUpdateOnVoteYes_8_atomic_Participant_Abort_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
   returns (first_commit: bool);
  requires true;
  requires !(AllocatedXids[first_xid] && VotesEqCoordinatorState(votes, state, first_xid));
  requires participantMid(second_mid);
  requires xUndecidedOrAborted(state[second_xid]);
  requires Aborted(state[second_xid][CoordinatorMid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> !(AllocatedXids[first_xid] && VotesEqCoordinatorState(votes, state, first_xid));



implementation CommutativityChecker_atomic_StateUpdateOnVoteNo_8_atomic_Participant_Abort_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
   returns (first_abort: bool)
{

  first_anon0:
    first_abort := votes[first_xid] != -1;
    votes[first_xid] := -1;
    state[first_xid][CoordinatorMid] := (if first_abort then ABORTED() else state[first_xid][CoordinatorMid]);
    goto second_anon0;

  second_anon0:
    state[second_xid][second_mid] := ABORTED();
    return;
}



procedure CommutativityChecker_atomic_StateUpdateOnVoteNo_8_atomic_Participant_Abort_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
   returns (first_abort: bool);
  requires true;
  requires AllocatedXids[first_xid];
  requires !Committed(state[first_xid][CoordinatorMid]);
  requires participantMid(second_mid);
  requires xUndecidedOrAborted(state[second_xid]);
  requires Aborted(state[second_xid][CoordinatorMid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> AllocatedXids == old(AllocatedXids)
       && state
         == old(state)[second_xid := old(state)[second_xid][second_mid := ABORTED()]][first_xid := old(state)[second_xid := old(state)[second_xid][second_mid := ABORTED()]][first_xid][CoordinatorMid := (if old(votes)[first_xid] != -1
           then ABORTED()
           else old(state)[second_xid := old(state)[second_xid][second_mid := ABORTED()]][first_xid][CoordinatorMid])]]
       && votes == old(votes)[first_xid := -1]
       && (first_abort <==> old(votes)[first_xid] != -1);



implementation GatePreservationChecker_atomic_Participant_Abort_8_atomic_StateUpdateOnVoteNo_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
   returns (second_abort: bool)
{

  second_anon0:
    second_abort := votes[second_xid] != -1;
    votes[second_xid] := -1;
    state[second_xid][CoordinatorMid] := (if second_abort then ABORTED() else state[second_xid][CoordinatorMid]);
    return;
}



procedure GatePreservationChecker_atomic_Participant_Abort_8_atomic_StateUpdateOnVoteNo_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
   returns (second_abort: bool);
  requires true;
  requires AllocatedXids[second_xid];
  requires !Committed(state[second_xid][CoordinatorMid]);
  requires participantMid(first_mid);
  requires xUndecidedOrAborted(state[first_xid]);
  requires Aborted(state[first_xid][CoordinatorMid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true ==> participantMid(first_mid);
  ensures true ==> xUndecidedOrAborted(state[first_xid]);
  ensures true ==> Aborted(state[first_xid][CoordinatorMid]);



implementation FailurePreservationChecker_atomic_StateUpdateOnVoteNo_8_atomic_Participant_Abort_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
   returns (first_abort: bool)
{

  second_anon0:
    state[second_xid][second_mid] := ABORTED();
    return;
}



procedure FailurePreservationChecker_atomic_StateUpdateOnVoteNo_8_atomic_Participant_Abort_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
   returns (first_abort: bool);
  requires true;
  requires !(AllocatedXids[first_xid] && !Committed(state[first_xid][CoordinatorMid]));
  requires participantMid(second_mid);
  requires xUndecidedOrAborted(state[second_xid]);
  requires Aborted(state[second_xid][CoordinatorMid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> !(AllocatedXids[first_xid] && !Committed(state[first_xid][CoordinatorMid]));



implementation CommutativityChecker_atomic_Participant_Commit_8_atomic_Participant_Abort_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
{

  first_anon0:
    state[first_xid][first_mid] := COMMITTED();
    goto second_anon0;

  second_anon0:
    state[second_xid][second_mid] := ABORTED();
    return;
}



procedure CommutativityChecker_atomic_Participant_Commit_8_atomic_Participant_Abort_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid);
  requires true;
  requires participantMid(first_mid);
  requires xUndecidedOrCommitted(state[first_xid]);
  requires Committed(state[first_xid][CoordinatorMid]);
  requires participantMid(second_mid);
  requires xUndecidedOrAborted(state[second_xid]);
  requires Aborted(state[second_xid][CoordinatorMid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> state
       == old(state)[second_xid := old(state)[second_xid][second_mid := ABORTED()]][first_xid := old(state)[second_xid := old(state)[second_xid][second_mid := ABORTED()]][first_xid][first_mid := COMMITTED()]];



implementation GatePreservationChecker_atomic_Participant_Abort_8_atomic_Participant_Commit_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
{

  second_anon0:
    state[second_xid][second_mid] := COMMITTED();
    return;
}



procedure GatePreservationChecker_atomic_Participant_Abort_8_atomic_Participant_Commit_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid);
  requires true;
  requires participantMid(second_mid);
  requires xUndecidedOrCommitted(state[second_xid]);
  requires Committed(state[second_xid][CoordinatorMid]);
  requires participantMid(first_mid);
  requires xUndecidedOrAborted(state[first_xid]);
  requires Aborted(state[first_xid][CoordinatorMid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true ==> participantMid(first_mid);
  ensures true ==> xUndecidedOrAborted(state[first_xid]);
  ensures true ==> Aborted(state[first_xid][CoordinatorMid]);



implementation FailurePreservationChecker_atomic_Participant_Commit_8_atomic_Participant_Abort_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
{

  second_anon0:
    state[second_xid][second_mid] := ABORTED();
    return;
}



procedure FailurePreservationChecker_atomic_Participant_Commit_8_atomic_Participant_Abort_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid);
  requires true;
  requires !(
    participantMid(first_mid)
     && xUndecidedOrCommitted(state[first_xid])
     && Committed(state[first_xid][CoordinatorMid]));
  requires participantMid(second_mid);
  requires xUndecidedOrAborted(state[second_xid]);
  requires Aborted(state[second_xid][CoordinatorMid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> !(
      participantMid(first_mid)
       && xUndecidedOrCommitted(state[first_xid])
       && Committed(state[first_xid][CoordinatorMid]));



implementation CommutativityChecker_atomic_Participant_Abort_8_atomic_Participant_Abort_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
{

  first_anon0:
    state[first_xid][first_mid] := ABORTED();
    goto second_anon0;

  second_anon0:
    state[second_xid][second_mid] := ABORTED();
    return;
}



procedure CommutativityChecker_atomic_Participant_Abort_8_atomic_Participant_Abort_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid);
  requires true;
  requires participantMid(first_mid);
  requires xUndecidedOrAborted(state[first_xid]);
  requires Aborted(state[first_xid][CoordinatorMid]);
  requires participantMid(second_mid);
  requires xUndecidedOrAborted(state[second_xid]);
  requires Aborted(state[second_xid][CoordinatorMid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> state
       == old(state)[second_xid := old(state)[second_xid][second_mid := ABORTED()]][first_xid := old(state)[second_xid := old(state)[second_xid][second_mid := ABORTED()]][first_xid][first_mid := ABORTED()]];



implementation GatePreservationChecker_atomic_Participant_Abort_8_atomic_Participant_Abort_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
{

  second_anon0:
    state[second_xid][second_mid] := ABORTED();
    return;
}



procedure GatePreservationChecker_atomic_Participant_Abort_8_atomic_Participant_Abort_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid);
  requires true;
  requires participantMid(second_mid);
  requires xUndecidedOrAborted(state[second_xid]);
  requires Aborted(state[second_xid][CoordinatorMid]);
  requires participantMid(first_mid);
  requires xUndecidedOrAborted(state[first_xid]);
  requires Aborted(state[first_xid][CoordinatorMid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true ==> participantMid(first_mid);
  ensures true ==> xUndecidedOrAborted(state[first_xid]);
  ensures true ==> Aborted(state[first_xid][CoordinatorMid]);



implementation FailurePreservationChecker_atomic_Participant_Abort_8_atomic_Participant_Abort_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid)
{

  second_anon0:
    state[second_xid][second_mid] := ABORTED();
    return;
}



procedure FailurePreservationChecker_atomic_Participant_Abort_8_atomic_Participant_Abort_8(first_xid: Xid, first_mid: Mid, second_xid: Xid, second_mid: Mid);
  requires true;
  requires !(
    participantMid(first_mid)
     && xUndecidedOrAborted(state[first_xid])
     && Aborted(state[first_xid][CoordinatorMid]));
  requires participantMid(second_mid);
  requires xUndecidedOrAborted(state[second_xid]);
  requires Aborted(state[second_xid][CoordinatorMid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> !(
      participantMid(first_mid)
       && xUndecidedOrAborted(state[first_xid])
       && Aborted(state[first_xid][CoordinatorMid]));



implementation CommutativityChecker_atomic_AllocateXid_8_atomic_Participant_Abort_8(second_xid: Xid, second_mid: Mid)
   returns (first_xid: Xid, first_pairs: [Pair]bool)
{

  first_anon0:
    assume !AllocatedXids[first_xid];
    assume state[first_xid] == (lambda first_j: Mid :: UNDECIDED());
    first_pairs := (lambda first_p: Pair :: pair(first_xid, mid#Pair(first_p), first_p));
    AllocatedXids[first_xid] := true;
    goto second_anon0;

  second_anon0:
    state[second_xid][second_mid] := ABORTED();
    return;
}



procedure CommutativityChecker_atomic_AllocateXid_8_atomic_Participant_Abort_8(second_xid: Xid, second_mid: Mid)
   returns (first_xid: Xid, first_pairs: [Pair]bool);
  requires true;
  requires participantMid(second_mid);
  requires xUndecidedOrAborted(state[second_xid]);
  requires Aborted(state[second_xid][CoordinatorMid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> AllocatedXids == old(AllocatedXids)[first_xid := true]
       && state
         == old(state)[second_xid := old(state)[second_xid][second_mid := ABORTED()]]
       && first_xid == first_xid
       && first_pairs
         == (lambda first_p: Pair :: pair(first_xid, mid#Pair(first_p), first_p))
       && old(state)[second_xid := old(state)[second_xid][second_mid := ABORTED()]][first_xid]
         == (lambda first_j: Mid :: UNDECIDED())
       && !old(AllocatedXids)[first_xid];



implementation CommutativityChecker_atomic_Coordinator_VoteYes_9_atomic_Coordinator_VoteYes_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair)
{
  var first_oldState: XState;
  var first_newState: XState;
  var second_oldState: XState;
  var second_newState: XState;

  first_anon0:
    B[first_pair] := true;
    first_oldState := state[first_xid];
    goto first_anon2_Then, first_anon2_Else;

  first_anon2_Else:
    goto second_anon0;

  first_anon2_Then:
    assume xAllParticipantsInB(first_xid, B);
    assume xConsistentExtension(first_oldState, first_newState);
    state[first_xid] := first_newState;
    goto second_anon0;

  second_anon0:
    B[second_pair] := true;
    second_oldState := state[second_xid];
    goto second_anon2_Then, second_anon2_Else;

  second_anon2_Else:
    return;

  second_anon2_Then:
    assume xAllParticipantsInB(second_xid, B);
    assume xConsistentExtension(second_oldState, second_newState);
    state[second_xid] := second_newState;
    return;
}



procedure CommutativityChecker_atomic_Coordinator_VoteYes_9_atomic_Coordinator_VoteYes_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair);
  requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairCollector(first_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(second_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
         == linear_pair_MapConstBool(true));
  requires AllocatedXids[first_xid];
  requires pair(first_xid, first_mid, first_pair);
  requires xConsistent(state[first_xid]);
  requires AllocatedXids[second_xid];
  requires pair(second_xid, second_mid, second_pair);
  requires xConsistent(state[second_xid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> (exists #tmp_0_second_newState: XState, #tmp_1_first_newState: XState :: 
        AllocatedXids == old(AllocatedXids)
           && state
             == old(state)[second_xid := #tmp_0_second_newState][first_xid := #tmp_1_first_newState]
           && B == old(B)[second_pair := true][first_pair := true]
           && xConsistentExtension(old(state)[second_xid := #tmp_0_second_newState][first_xid], 
            #tmp_1_first_newState)
           && xAllParticipantsInB(first_xid, old(B)[second_pair := true][first_pair := true])
           && xConsistentExtension(old(state)[second_xid], #tmp_0_second_newState)
           && xAllParticipantsInB(second_xid, old(B)[second_pair := true]))
       || (exists #tmp_0_second_newState: XState :: 
        AllocatedXids == old(AllocatedXids)
           && state == old(state)[second_xid := #tmp_0_second_newState]
           && B == old(B)[second_pair := true][first_pair := true]
           && xConsistentExtension(old(state)[second_xid], #tmp_0_second_newState)
           && xAllParticipantsInB(second_xid, old(B)[second_pair := true]))
       || (exists #tmp_1_first_newState: XState :: 
        AllocatedXids == old(AllocatedXids)
           && state == old(state)[first_xid := #tmp_1_first_newState]
           && B == old(B)[second_pair := true][first_pair := true]
           && xConsistentExtension(old(state)[first_xid], #tmp_1_first_newState)
           && xAllParticipantsInB(first_xid, old(B)[second_pair := true][first_pair := true]))
       || (
        AllocatedXids == old(AllocatedXids)
         && state == old(state)
         && B == old(B)[second_pair := true][first_pair := true]);



implementation GatePreservationChecker_atomic_Coordinator_VoteYes_9_atomic_Coordinator_VoteYes_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair)
{
  var second_oldState: XState;
  var second_newState: XState;

  second_anon0:
    B[second_pair] := true;
    second_oldState := state[second_xid];
    goto second_anon2_Then, second_anon2_Else;

  second_anon2_Else:
    return;

  second_anon2_Then:
    assume xAllParticipantsInB(second_xid, B);
    assume xConsistentExtension(second_oldState, second_newState);
    state[second_xid] := second_newState;
    return;
}



procedure GatePreservationChecker_atomic_Coordinator_VoteYes_9_atomic_Coordinator_VoteYes_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair);
  requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairCollector(first_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(second_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
         == linear_pair_MapConstBool(true));
  requires AllocatedXids[second_xid];
  requires pair(second_xid, second_mid, second_pair);
  requires xConsistent(state[second_xid]);
  requires AllocatedXids[first_xid];
  requires pair(first_xid, first_mid, first_pair);
  requires xConsistent(state[first_xid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(PairCollector(first_pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true))
     ==> AllocatedXids[first_xid];
  ensures (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(PairCollector(first_pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true))
     ==> pair(first_xid, first_mid, first_pair);
  ensures (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(PairCollector(first_pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true))
     ==> xConsistent(state[first_xid]);



implementation FailurePreservationChecker_atomic_Coordinator_VoteYes_9_atomic_Coordinator_VoteYes_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair)
{
  var second_oldState: XState;
  var second_newState: XState;

  second_anon0:
    B[second_pair] := true;
    second_oldState := state[second_xid];
    goto second_anon2_Then, second_anon2_Else;

  second_anon2_Else:
    return;

  second_anon2_Then:
    assume xAllParticipantsInB(second_xid, B);
    assume xConsistentExtension(second_oldState, second_newState);
    state[second_xid] := second_newState;
    return;
}



procedure FailurePreservationChecker_atomic_Coordinator_VoteYes_9_atomic_Coordinator_VoteYes_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair);
  requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairCollector(first_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(second_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
         == linear_pair_MapConstBool(true));
  requires !(
    AllocatedXids[first_xid]
     && pair(first_xid, first_mid, first_pair)
     && xConsistent(state[first_xid]));
  requires AllocatedXids[second_xid];
  requires pair(second_xid, second_mid, second_pair);
  requires xConsistent(state[second_xid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(PairCollector(first_pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true))
     ==> !(
      AllocatedXids[first_xid]
       && pair(first_xid, first_mid, first_pair)
       && xConsistent(state[first_xid]));



implementation CommutativityChecker_atomic_Coordinator_VoteNo_9_atomic_Coordinator_VoteYes_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair)
{
  var first_oldState: XState;
  var first_newState: XState;
  var second_oldState: XState;
  var second_newState: XState;

  first_anon0:
    first_oldState := state[first_xid];
    assume xUndecidedOrAborted(first_newState);
    assume xConsistentExtension(first_oldState, first_newState);
    state[first_xid] := first_newState;
    goto second_anon0;

  second_anon0:
    B[second_pair] := true;
    second_oldState := state[second_xid];
    goto second_anon2_Then, second_anon2_Else;

  second_anon2_Else:
    return;

  second_anon2_Then:
    assume xAllParticipantsInB(second_xid, B);
    assume xConsistentExtension(second_oldState, second_newState);
    state[second_xid] := second_newState;
    return;
}



procedure CommutativityChecker_atomic_Coordinator_VoteNo_9_atomic_Coordinator_VoteYes_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair);
  requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairCollector(first_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(second_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
         == linear_pair_MapConstBool(true));
  requires AllocatedXids[first_xid];
  requires pair(first_xid, first_mid, first_pair);
  requires xUndecidedOrAborted(state[first_xid]);
  requires AllocatedXids[second_xid];
  requires pair(second_xid, second_mid, second_pair);
  requires xConsistent(state[second_xid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> (exists #tmp_0_second_newState: XState, #tmp_1_first_newState: XState :: 
        AllocatedXids == old(AllocatedXids)
           && state
             == old(state)[second_xid := #tmp_0_second_newState][first_xid := #tmp_1_first_newState]
           && B == old(B)[second_pair := true]
           && xConsistentExtension(old(state)[second_xid := #tmp_0_second_newState][first_xid], 
            #tmp_1_first_newState)
           && xUndecidedOrAborted(#tmp_1_first_newState)
           && xConsistentExtension(old(state)[second_xid], #tmp_0_second_newState)
           && xAllParticipantsInB(second_xid, old(B)[second_pair := true]))
       || (exists #tmp_1_first_newState: XState :: 
        AllocatedXids == old(AllocatedXids)
           && state == old(state)[first_xid := #tmp_1_first_newState]
           && B == old(B)[second_pair := true]
           && xConsistentExtension(old(state)[first_xid], #tmp_1_first_newState)
           && xUndecidedOrAborted(#tmp_1_first_newState));



implementation GatePreservationChecker_atomic_Coordinator_VoteYes_9_atomic_Coordinator_VoteNo_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair)
{
  var second_oldState: XState;
  var second_newState: XState;

  second_anon0:
    second_oldState := state[second_xid];
    assume xUndecidedOrAborted(second_newState);
    assume xConsistentExtension(second_oldState, second_newState);
    state[second_xid] := second_newState;
    return;
}



procedure GatePreservationChecker_atomic_Coordinator_VoteYes_9_atomic_Coordinator_VoteNo_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair);
  requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairCollector(first_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(second_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  requires AllocatedXids[second_xid];
  requires pair(second_xid, second_mid, second_pair);
  requires xUndecidedOrAborted(state[second_xid]);
  requires AllocatedXids[first_xid];
  requires pair(first_xid, first_mid, first_pair);
  requires xConsistent(state[first_xid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true ==> AllocatedXids[first_xid];
  ensures true ==> pair(first_xid, first_mid, first_pair);
  ensures true ==> xConsistent(state[first_xid]);



implementation FailurePreservationChecker_atomic_Coordinator_VoteNo_9_atomic_Coordinator_VoteYes_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair)
{
  var second_oldState: XState;
  var second_newState: XState;

  second_anon0:
    B[second_pair] := true;
    second_oldState := state[second_xid];
    goto second_anon2_Then, second_anon2_Else;

  second_anon2_Else:
    return;

  second_anon2_Then:
    assume xAllParticipantsInB(second_xid, B);
    assume xConsistentExtension(second_oldState, second_newState);
    state[second_xid] := second_newState;
    return;
}



procedure FailurePreservationChecker_atomic_Coordinator_VoteNo_9_atomic_Coordinator_VoteYes_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair);
  requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairCollector(first_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(second_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
         == linear_pair_MapConstBool(true));
  requires !(
    AllocatedXids[first_xid]
     && pair(first_xid, first_mid, first_pair)
     && xUndecidedOrAborted(state[first_xid]));
  requires AllocatedXids[second_xid];
  requires pair(second_xid, second_mid, second_pair);
  requires xConsistent(state[second_xid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(PairCollector(first_pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true))
     ==> !(
      AllocatedXids[first_xid]
       && pair(first_xid, first_mid, first_pair)
       && xUndecidedOrAborted(state[first_xid]));



implementation CommutativityChecker_atomic_SetParticipantAborted_9_atomic_Coordinator_VoteYes_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair)
{
  var second_oldState: XState;
  var second_newState: XState;

  first_anon0:
    state[first_xid][first_mid] := ABORTED();
    goto second_anon0;

  second_anon0:
    B[second_pair] := true;
    second_oldState := state[second_xid];
    goto second_anon2_Then, second_anon2_Else;

  second_anon2_Else:
    return;

  second_anon2_Then:
    assume xAllParticipantsInB(second_xid, B);
    assume xConsistentExtension(second_oldState, second_newState);
    state[second_xid] := second_newState;
    return;
}



procedure CommutativityChecker_atomic_SetParticipantAborted_9_atomic_Coordinator_VoteYes_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair);
  requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairCollector(first_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(second_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
         == linear_pair_MapConstBool(true));
  requires pair(first_xid, first_mid, first_pair);
  requires xUndecidedOrAborted(state[first_xid]);
  requires AllocatedXids[second_xid];
  requires pair(second_xid, second_mid, second_pair);
  requires xConsistent(state[second_xid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> (exists #tmp_0_second_newState: XState :: 
        state
             == old(state)[second_xid := #tmp_0_second_newState][first_xid := old(state)[second_xid := #tmp_0_second_newState][first_xid][first_mid := ABORTED()]]
           && AllocatedXids == old(AllocatedXids)
           && B == old(B)[second_pair := true]
           && xConsistentExtension(old(state)[second_xid], #tmp_0_second_newState)
           && xAllParticipantsInB(second_xid, old(B)[second_pair := true]))
       || (
        state == old(state)[first_xid := old(state)[first_xid][first_mid := ABORTED()]]
         && AllocatedXids == old(AllocatedXids)
         && B == old(B)[second_pair := true]);



implementation GatePreservationChecker_atomic_Coordinator_VoteYes_9_atomic_SetParticipantAborted_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair)
{

  second_anon0:
    state[second_xid][second_mid] := ABORTED();
    return;
}



procedure GatePreservationChecker_atomic_Coordinator_VoteYes_9_atomic_SetParticipantAborted_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair);
  requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairCollector(first_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(second_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  requires pair(second_xid, second_mid, second_pair);
  requires xUndecidedOrAborted(state[second_xid]);
  requires AllocatedXids[first_xid];
  requires pair(first_xid, first_mid, first_pair);
  requires xConsistent(state[first_xid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true ==> AllocatedXids[first_xid];
  ensures true ==> pair(first_xid, first_mid, first_pair);
  ensures true ==> xConsistent(state[first_xid]);



implementation FailurePreservationChecker_atomic_SetParticipantAborted_9_atomic_Coordinator_VoteYes_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair)
{
  var second_oldState: XState;
  var second_newState: XState;

  second_anon0:
    B[second_pair] := true;
    second_oldState := state[second_xid];
    goto second_anon2_Then, second_anon2_Else;

  second_anon2_Else:
    return;

  second_anon2_Then:
    assume xAllParticipantsInB(second_xid, B);
    assume xConsistentExtension(second_oldState, second_newState);
    state[second_xid] := second_newState;
    return;
}



procedure FailurePreservationChecker_atomic_SetParticipantAborted_9_atomic_Coordinator_VoteYes_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair);
  requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairCollector(first_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(second_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
         == linear_pair_MapConstBool(true));
  requires !(pair(first_xid, first_mid, first_pair)
     && xUndecidedOrAborted(state[first_xid]));
  requires AllocatedXids[second_xid];
  requires pair(second_xid, second_mid, second_pair);
  requires xConsistent(state[second_xid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(PairCollector(first_pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true))
     ==> !(pair(first_xid, first_mid, first_pair)
       && xUndecidedOrAborted(state[first_xid]));



implementation CommutativityChecker_atomic_AllocateXid_9_atomic_Coordinator_VoteYes_9(second_xid: Xid, second_mid: Mid, second_pair: Pair)
   returns (first_xid: Xid, first_pairs: [Pair]bool)
{
  var second_oldState: XState;
  var second_newState: XState;

  first_anon0:
    assume !AllocatedXids[first_xid];
    assume state[first_xid] == (lambda first_j: Mid :: UNDECIDED());
    first_pairs := (lambda first_p: Pair :: pair(first_xid, mid#Pair(first_p), first_p));
    AllocatedXids[first_xid] := true;
    goto second_anon0;

  second_anon0:
    B[second_pair] := true;
    second_oldState := state[second_xid];
    goto second_anon2_Then, second_anon2_Else;

  second_anon2_Else:
    return;

  second_anon2_Then:
    assume xAllParticipantsInB(second_xid, B);
    assume xConsistentExtension(second_oldState, second_newState);
    state[second_xid] := second_newState;
    return;
}



procedure CommutativityChecker_atomic_AllocateXid_9_atomic_Coordinator_VoteYes_9(second_xid: Xid, second_mid: Mid, second_pair: Pair)
   returns (first_xid: Xid, first_pairs: [Pair]bool);
  requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairCollector(second_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  requires AllocatedXids[second_xid];
  requires pair(second_xid, second_mid, second_pair);
  requires xConsistent(state[second_xid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures (exists partition_pair: [Pair]int :: 
        linear_pair_MapImp(PairSetCollector(first_pairs), 
              linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
             == linear_pair_MapConstBool(true)
           && linear_pair_MapImp(PairSetCollector(B), 
              linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
             == linear_pair_MapConstBool(true))
       && (exists partition_pair: [Pair]int :: 
        linear_pair_MapImp(PairSetCollector(first_pairs), 
              linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
             == linear_pair_MapConstBool(true)
           && linear_pair_MapImp(PairSetCollector(B), 
              linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
             == linear_pair_MapConstBool(true))
     ==> (exists #tmp_0_second_newState: XState :: 
        AllocatedXids == old(AllocatedXids)[first_xid := true]
           && state == old(state)[second_xid := #tmp_0_second_newState]
           && B == old(B)[second_pair := true]
           && first_xid == first_xid
           && first_pairs
             == (lambda first_p: Pair :: pair(first_xid, mid#Pair(first_p), first_p))
           && old(state)[second_xid := #tmp_0_second_newState][first_xid]
             == (lambda first_j: Mid :: UNDECIDED())
           && !old(AllocatedXids)[first_xid]
           && xConsistentExtension(old(state)[second_xid], #tmp_0_second_newState)
           && xAllParticipantsInB(second_xid, old(B)[second_pair := true]))
       || (
        AllocatedXids == old(AllocatedXids)[first_xid := true]
         && state == old(state)
         && B == old(B)[second_pair := true]
         && first_xid == first_xid
         && first_pairs
           == (lambda first_p: Pair :: pair(first_xid, mid#Pair(first_p), first_p))
         && old(state)[first_xid] == (lambda first_j: Mid :: UNDECIDED())
         && !old(AllocatedXids)[first_xid]);



implementation GatePreservationChecker_atomic_Coordinator_VoteYes_9_atomic_AllocateXid_9(first_xid: Xid, first_mid: Mid, first_pair: Pair)
   returns (second_xid: Xid, second_pairs: [Pair]bool)
{

  second_anon0:
    assume !AllocatedXids[second_xid];
    assume state[second_xid] == (lambda second_j: Mid :: UNDECIDED());
    second_pairs := (lambda second_p: Pair :: pair(second_xid, mid#Pair(second_p), second_p));
    AllocatedXids[second_xid] := true;
    return;
}



procedure GatePreservationChecker_atomic_Coordinator_VoteYes_9_atomic_AllocateXid_9(first_xid: Xid, first_mid: Mid, first_pair: Pair)
   returns (second_xid: Xid, second_pairs: [Pair]bool);
  requires true;
  requires AllocatedXids[first_xid];
  requires pair(first_xid, first_mid, first_pair);
  requires xConsistent(state[first_xid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(PairCollector(first_pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(second_pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true))
     ==> AllocatedXids[first_xid];
  ensures (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(PairCollector(first_pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(second_pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true))
     ==> pair(first_xid, first_mid, first_pair);
  ensures (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(PairCollector(first_pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(second_pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true))
     ==> xConsistent(state[first_xid]);



implementation CommutativityChecker_atomic_Coordinator_VoteYes_9_atomic_Coordinator_VoteNo_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair)
{
  var first_oldState: XState;
  var first_newState: XState;
  var second_oldState: XState;
  var second_newState: XState;

  first_anon0:
    B[first_pair] := true;
    first_oldState := state[first_xid];
    goto first_anon2_Then, first_anon2_Else;

  first_anon2_Else:
    goto second_anon0;

  first_anon2_Then:
    assume xAllParticipantsInB(first_xid, B);
    assume xConsistentExtension(first_oldState, first_newState);
    state[first_xid] := first_newState;
    goto second_anon0;

  second_anon0:
    second_oldState := state[second_xid];
    assume xUndecidedOrAborted(second_newState);
    assume xConsistentExtension(second_oldState, second_newState);
    state[second_xid] := second_newState;
    return;
}



procedure CommutativityChecker_atomic_Coordinator_VoteYes_9_atomic_Coordinator_VoteNo_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair);
  requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairCollector(first_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(second_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
         == linear_pair_MapConstBool(true));
  requires AllocatedXids[first_xid];
  requires pair(first_xid, first_mid, first_pair);
  requires xConsistent(state[first_xid]);
  requires AllocatedXids[second_xid];
  requires pair(second_xid, second_mid, second_pair);
  requires xUndecidedOrAborted(state[second_xid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> (exists #tmp_0_second_newState: XState, #tmp_1_first_newState: XState :: 
        AllocatedXids == old(AllocatedXids)
           && state
             == old(state)[second_xid := #tmp_0_second_newState][first_xid := #tmp_1_first_newState]
           && B == old(B)[first_pair := true]
           && xConsistentExtension(old(state)[second_xid := #tmp_0_second_newState][first_xid], 
            #tmp_1_first_newState)
           && xAllParticipantsInB(first_xid, old(B)[first_pair := true])
           && xConsistentExtension(old(state)[second_xid], #tmp_0_second_newState)
           && xUndecidedOrAborted(#tmp_0_second_newState))
       || (exists #tmp_0_second_newState: XState :: 
        AllocatedXids == old(AllocatedXids)
           && state == old(state)[second_xid := #tmp_0_second_newState]
           && B == old(B)[first_pair := true]
           && xConsistentExtension(old(state)[second_xid], #tmp_0_second_newState)
           && xUndecidedOrAborted(#tmp_0_second_newState));



implementation GatePreservationChecker_atomic_Coordinator_VoteNo_9_atomic_Coordinator_VoteYes_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair)
{
  var second_oldState: XState;
  var second_newState: XState;

  second_anon0:
    B[second_pair] := true;
    second_oldState := state[second_xid];
    goto second_anon2_Then, second_anon2_Else;

  second_anon2_Else:
    return;

  second_anon2_Then:
    assume xAllParticipantsInB(second_xid, B);
    assume xConsistentExtension(second_oldState, second_newState);
    state[second_xid] := second_newState;
    return;
}



procedure GatePreservationChecker_atomic_Coordinator_VoteNo_9_atomic_Coordinator_VoteYes_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair);
  requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairCollector(first_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(second_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
         == linear_pair_MapConstBool(true));
  requires AllocatedXids[second_xid];
  requires pair(second_xid, second_mid, second_pair);
  requires xConsistent(state[second_xid]);
  requires AllocatedXids[first_xid];
  requires pair(first_xid, first_mid, first_pair);
  requires xUndecidedOrAborted(state[first_xid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(PairCollector(first_pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true))
     ==> AllocatedXids[first_xid];
  ensures (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(PairCollector(first_pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true))
     ==> pair(first_xid, first_mid, first_pair);
  ensures (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(PairCollector(first_pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true))
     ==> xUndecidedOrAborted(state[first_xid]);



implementation FailurePreservationChecker_atomic_Coordinator_VoteYes_9_atomic_Coordinator_VoteNo_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair)
{
  var second_oldState: XState;
  var second_newState: XState;

  second_anon0:
    second_oldState := state[second_xid];
    assume xUndecidedOrAborted(second_newState);
    assume xConsistentExtension(second_oldState, second_newState);
    state[second_xid] := second_newState;
    return;
}



procedure FailurePreservationChecker_atomic_Coordinator_VoteYes_9_atomic_Coordinator_VoteNo_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair);
  requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairCollector(first_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(second_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  requires !(
    AllocatedXids[first_xid]
     && pair(first_xid, first_mid, first_pair)
     && xConsistent(state[first_xid]));
  requires AllocatedXids[second_xid];
  requires pair(second_xid, second_mid, second_pair);
  requires xUndecidedOrAborted(state[second_xid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> !(
      AllocatedXids[first_xid]
       && pair(first_xid, first_mid, first_pair)
       && xConsistent(state[first_xid]));



implementation CommutativityChecker_atomic_Coordinator_VoteNo_9_atomic_Coordinator_VoteNo_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair)
{
  var first_oldState: XState;
  var first_newState: XState;
  var second_oldState: XState;
  var second_newState: XState;

  first_anon0:
    first_oldState := state[first_xid];
    assume xUndecidedOrAborted(first_newState);
    assume xConsistentExtension(first_oldState, first_newState);
    state[first_xid] := first_newState;
    goto second_anon0;

  second_anon0:
    second_oldState := state[second_xid];
    assume xUndecidedOrAborted(second_newState);
    assume xConsistentExtension(second_oldState, second_newState);
    state[second_xid] := second_newState;
    return;
}



procedure CommutativityChecker_atomic_Coordinator_VoteNo_9_atomic_Coordinator_VoteNo_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair);
  requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairCollector(first_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(second_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  requires AllocatedXids[first_xid];
  requires pair(first_xid, first_mid, first_pair);
  requires xUndecidedOrAborted(state[first_xid]);
  requires AllocatedXids[second_xid];
  requires pair(second_xid, second_mid, second_pair);
  requires xUndecidedOrAborted(state[second_xid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> (exists #tmp_0_second_newState: XState, #tmp_1_first_newState: XState :: 
      AllocatedXids == old(AllocatedXids)
         && state
           == old(state)[second_xid := #tmp_0_second_newState][first_xid := #tmp_1_first_newState]
         && xConsistentExtension(old(state)[second_xid := #tmp_0_second_newState][first_xid], 
          #tmp_1_first_newState)
         && xUndecidedOrAborted(#tmp_1_first_newState)
         && xConsistentExtension(old(state)[second_xid], #tmp_0_second_newState)
         && xUndecidedOrAborted(#tmp_0_second_newState));



implementation GatePreservationChecker_atomic_Coordinator_VoteNo_9_atomic_Coordinator_VoteNo_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair)
{
  var second_oldState: XState;
  var second_newState: XState;

  second_anon0:
    second_oldState := state[second_xid];
    assume xUndecidedOrAborted(second_newState);
    assume xConsistentExtension(second_oldState, second_newState);
    state[second_xid] := second_newState;
    return;
}



procedure GatePreservationChecker_atomic_Coordinator_VoteNo_9_atomic_Coordinator_VoteNo_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair);
  requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairCollector(first_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(second_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  requires AllocatedXids[second_xid];
  requires pair(second_xid, second_mid, second_pair);
  requires xUndecidedOrAborted(state[second_xid]);
  requires AllocatedXids[first_xid];
  requires pair(first_xid, first_mid, first_pair);
  requires xUndecidedOrAborted(state[first_xid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true ==> AllocatedXids[first_xid];
  ensures true ==> pair(first_xid, first_mid, first_pair);
  ensures true ==> xUndecidedOrAborted(state[first_xid]);



implementation FailurePreservationChecker_atomic_Coordinator_VoteNo_9_atomic_Coordinator_VoteNo_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair)
{
  var second_oldState: XState;
  var second_newState: XState;

  second_anon0:
    second_oldState := state[second_xid];
    assume xUndecidedOrAborted(second_newState);
    assume xConsistentExtension(second_oldState, second_newState);
    state[second_xid] := second_newState;
    return;
}



procedure FailurePreservationChecker_atomic_Coordinator_VoteNo_9_atomic_Coordinator_VoteNo_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair);
  requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairCollector(first_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(second_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  requires !(
    AllocatedXids[first_xid]
     && pair(first_xid, first_mid, first_pair)
     && xUndecidedOrAborted(state[first_xid]));
  requires AllocatedXids[second_xid];
  requires pair(second_xid, second_mid, second_pair);
  requires xUndecidedOrAborted(state[second_xid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> !(
      AllocatedXids[first_xid]
       && pair(first_xid, first_mid, first_pair)
       && xUndecidedOrAborted(state[first_xid]));



implementation CommutativityChecker_atomic_SetParticipantAborted_9_atomic_Coordinator_VoteNo_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair)
{
  var second_oldState: XState;
  var second_newState: XState;

  first_anon0:
    state[first_xid][first_mid] := ABORTED();
    goto second_anon0;

  second_anon0:
    second_oldState := state[second_xid];
    assume xUndecidedOrAborted(second_newState);
    assume xConsistentExtension(second_oldState, second_newState);
    state[second_xid] := second_newState;
    return;
}



procedure CommutativityChecker_atomic_SetParticipantAborted_9_atomic_Coordinator_VoteNo_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair);
  requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairCollector(first_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(second_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  requires pair(first_xid, first_mid, first_pair);
  requires xUndecidedOrAborted(state[first_xid]);
  requires AllocatedXids[second_xid];
  requires pair(second_xid, second_mid, second_pair);
  requires xUndecidedOrAborted(state[second_xid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> (exists #tmp_0_second_newState: XState :: 
      state
           == old(state)[second_xid := #tmp_0_second_newState][first_xid := old(state)[second_xid := #tmp_0_second_newState][first_xid][first_mid := ABORTED()]]
         && AllocatedXids == old(AllocatedXids)
         && xConsistentExtension(old(state)[second_xid], #tmp_0_second_newState)
         && xUndecidedOrAborted(#tmp_0_second_newState));



implementation GatePreservationChecker_atomic_Coordinator_VoteNo_9_atomic_SetParticipantAborted_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair)
{

  second_anon0:
    state[second_xid][second_mid] := ABORTED();
    return;
}



procedure GatePreservationChecker_atomic_Coordinator_VoteNo_9_atomic_SetParticipantAborted_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair);
  requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairCollector(first_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(second_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  requires pair(second_xid, second_mid, second_pair);
  requires xUndecidedOrAborted(state[second_xid]);
  requires AllocatedXids[first_xid];
  requires pair(first_xid, first_mid, first_pair);
  requires xUndecidedOrAborted(state[first_xid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true ==> AllocatedXids[first_xid];
  ensures true ==> pair(first_xid, first_mid, first_pair);
  ensures true ==> xUndecidedOrAborted(state[first_xid]);



implementation FailurePreservationChecker_atomic_SetParticipantAborted_9_atomic_Coordinator_VoteNo_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair)
{
  var second_oldState: XState;
  var second_newState: XState;

  second_anon0:
    second_oldState := state[second_xid];
    assume xUndecidedOrAborted(second_newState);
    assume xConsistentExtension(second_oldState, second_newState);
    state[second_xid] := second_newState;
    return;
}



procedure FailurePreservationChecker_atomic_SetParticipantAborted_9_atomic_Coordinator_VoteNo_9(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair);
  requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairCollector(first_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(second_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  requires !(pair(first_xid, first_mid, first_pair)
     && xUndecidedOrAborted(state[first_xid]));
  requires AllocatedXids[second_xid];
  requires pair(second_xid, second_mid, second_pair);
  requires xUndecidedOrAborted(state[second_xid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> !(pair(first_xid, first_mid, first_pair)
       && xUndecidedOrAborted(state[first_xid]));



implementation CommutativityChecker_atomic_AllocateXid_9_atomic_Coordinator_VoteNo_9(second_xid: Xid, second_mid: Mid, second_pair: Pair)
   returns (first_xid: Xid, first_pairs: [Pair]bool)
{
  var second_oldState: XState;
  var second_newState: XState;

  first_anon0:
    assume !AllocatedXids[first_xid];
    assume state[first_xid] == (lambda first_j: Mid :: UNDECIDED());
    first_pairs := (lambda first_p: Pair :: pair(first_xid, mid#Pair(first_p), first_p));
    AllocatedXids[first_xid] := true;
    goto second_anon0;

  second_anon0:
    second_oldState := state[second_xid];
    assume xUndecidedOrAborted(second_newState);
    assume xConsistentExtension(second_oldState, second_newState);
    state[second_xid] := second_newState;
    return;
}



procedure CommutativityChecker_atomic_AllocateXid_9_atomic_Coordinator_VoteNo_9(second_xid: Xid, second_mid: Mid, second_pair: Pair)
   returns (first_xid: Xid, first_pairs: [Pair]bool);
  requires true;
  requires AllocatedXids[second_xid];
  requires pair(second_xid, second_mid, second_pair);
  requires xUndecidedOrAborted(state[second_xid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> (exists #tmp_0_second_newState: XState :: 
      AllocatedXids == old(AllocatedXids)[first_xid := true]
         && state == old(state)[second_xid := #tmp_0_second_newState]
         && first_xid == first_xid
         && first_pairs
           == (lambda first_p: Pair :: pair(first_xid, mid#Pair(first_p), first_p))
         && old(state)[second_xid := #tmp_0_second_newState][first_xid]
           == (lambda first_j: Mid :: UNDECIDED())
         && !old(AllocatedXids)[first_xid]
         && xConsistentExtension(old(state)[second_xid], #tmp_0_second_newState)
         && xUndecidedOrAborted(#tmp_0_second_newState));



implementation GatePreservationChecker_atomic_Coordinator_VoteNo_9_atomic_AllocateXid_9(first_xid: Xid, first_mid: Mid, first_pair: Pair)
   returns (second_xid: Xid, second_pairs: [Pair]bool)
{

  second_anon0:
    assume !AllocatedXids[second_xid];
    assume state[second_xid] == (lambda second_j: Mid :: UNDECIDED());
    second_pairs := (lambda second_p: Pair :: pair(second_xid, mid#Pair(second_p), second_p));
    AllocatedXids[second_xid] := true;
    return;
}



procedure GatePreservationChecker_atomic_Coordinator_VoteNo_9_atomic_AllocateXid_9(first_xid: Xid, first_mid: Mid, first_pair: Pair)
   returns (second_xid: Xid, second_pairs: [Pair]bool);
  requires true;
  requires AllocatedXids[first_xid];
  requires pair(first_xid, first_mid, first_pair);
  requires xUndecidedOrAborted(state[first_xid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(PairCollector(first_pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(second_pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true))
     ==> AllocatedXids[first_xid];
  ensures (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(PairCollector(first_pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(second_pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true))
     ==> pair(first_xid, first_mid, first_pair);
  ensures (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(PairCollector(first_pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(second_pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true))
     ==> xUndecidedOrAborted(state[first_xid]);



implementation NonBlockingChecker_atomic_Coordinator_VoteYes_9(second_xid: Xid, second_mid: Mid, second_pair: Pair)
{

  L:
    assert true;
    return;
}



procedure NonBlockingChecker_atomic_Coordinator_VoteYes_9(second_xid: Xid, second_mid: Mid, second_pair: Pair);
  requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairCollector(second_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  requires AllocatedXids[second_xid];
  requires pair(second_xid, second_mid, second_pair);
  requires xConsistent(state[second_xid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



implementation NonBlockingChecker_atomic_Coordinator_VoteNo_9(second_xid: Xid, second_mid: Mid, second_pair: Pair)
{

  L:
    assert (exists #tmp_0_second_newState: XState :: 
      xConsistentExtension(old(state)[second_xid], #tmp_0_second_newState)
         && xUndecidedOrAborted(#tmp_0_second_newState));
    return;
}



procedure NonBlockingChecker_atomic_Coordinator_VoteNo_9(second_xid: Xid, second_mid: Mid, second_pair: Pair);
  requires true;
  requires AllocatedXids[second_xid];
  requires pair(second_xid, second_mid, second_pair);
  requires xUndecidedOrAborted(state[second_xid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



implementation CommutativityChecker_atomic_Participant_VoteReq_10_atomic_Participant_VoteReq_10(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair)
{
  var first_oldState: XState;
  var first_newState: XState;
  var second_oldState: XState;
  var second_newState: XState;

  first_anon0:
    first_oldState := state[first_xid];
    assume xConsistentExtension(first_oldState, first_newState);
    state[first_xid] := first_newState;
    goto second_anon0;

  second_anon0:
    second_oldState := state[second_xid];
    assume xConsistentExtension(second_oldState, second_newState);
    state[second_xid] := second_newState;
    return;
}



procedure CommutativityChecker_atomic_Participant_VoteReq_10_atomic_Participant_VoteReq_10(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair);
  requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairCollector(first_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(second_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  requires AllocatedXids[first_xid];
  requires pair(first_xid, first_mid, first_pair);
  requires xConsistent(state[first_xid]);
  requires AllocatedXids[second_xid];
  requires pair(second_xid, second_mid, second_pair);
  requires xConsistent(state[second_xid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> (exists #tmp_0_second_newState: XState, #tmp_1_first_newState: XState :: 
      AllocatedXids == old(AllocatedXids)
         && state
           == old(state)[second_xid := #tmp_0_second_newState][first_xid := #tmp_1_first_newState]
         && xConsistentExtension(old(state)[second_xid := #tmp_0_second_newState][first_xid], 
          #tmp_1_first_newState)
         && xConsistentExtension(old(state)[second_xid], #tmp_0_second_newState));



implementation GatePreservationChecker_atomic_Participant_VoteReq_10_atomic_Participant_VoteReq_10(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair)
{
  var second_oldState: XState;
  var second_newState: XState;

  second_anon0:
    second_oldState := state[second_xid];
    assume xConsistentExtension(second_oldState, second_newState);
    state[second_xid] := second_newState;
    return;
}



procedure GatePreservationChecker_atomic_Participant_VoteReq_10_atomic_Participant_VoteReq_10(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair);
  requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairCollector(first_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(second_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  requires AllocatedXids[second_xid];
  requires pair(second_xid, second_mid, second_pair);
  requires xConsistent(state[second_xid]);
  requires AllocatedXids[first_xid];
  requires pair(first_xid, first_mid, first_pair);
  requires xConsistent(state[first_xid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true ==> AllocatedXids[first_xid];
  ensures true ==> pair(first_xid, first_mid, first_pair);
  ensures true ==> xConsistent(state[first_xid]);



implementation FailurePreservationChecker_atomic_Participant_VoteReq_10_atomic_Participant_VoteReq_10(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair)
{
  var second_oldState: XState;
  var second_newState: XState;

  second_anon0:
    second_oldState := state[second_xid];
    assume xConsistentExtension(second_oldState, second_newState);
    state[second_xid] := second_newState;
    return;
}



procedure FailurePreservationChecker_atomic_Participant_VoteReq_10_atomic_Participant_VoteReq_10(first_xid: Xid, 
    first_mid: Mid, 
    first_pair: Pair, 
    second_xid: Xid, 
    second_mid: Mid, 
    second_pair: Pair);
  requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairCollector(first_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(second_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  requires !(
    AllocatedXids[first_xid]
     && pair(first_xid, first_mid, first_pair)
     && xConsistent(state[first_xid]));
  requires AllocatedXids[second_xid];
  requires pair(second_xid, second_mid, second_pair);
  requires xConsistent(state[second_xid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> !(
      AllocatedXids[first_xid]
       && pair(first_xid, first_mid, first_pair)
       && xConsistent(state[first_xid]));



implementation CommutativityChecker_atomic_AllocateXid_10_atomic_Participant_VoteReq_10(second_xid: Xid, second_mid: Mid, second_pair: Pair)
   returns (first_xid: Xid, first_pairs: [Pair]bool)
{
  var second_oldState: XState;
  var second_newState: XState;

  first_anon0:
    assume !AllocatedXids[first_xid];
    assume state[first_xid] == (lambda first_j: Mid :: UNDECIDED());
    first_pairs := (lambda first_p: Pair :: pair(first_xid, mid#Pair(first_p), first_p));
    AllocatedXids[first_xid] := true;
    goto second_anon0;

  second_anon0:
    second_oldState := state[second_xid];
    assume xConsistentExtension(second_oldState, second_newState);
    state[second_xid] := second_newState;
    return;
}



procedure CommutativityChecker_atomic_AllocateXid_10_atomic_Participant_VoteReq_10(second_xid: Xid, second_mid: Mid, second_pair: Pair)
   returns (first_xid: Xid, first_pairs: [Pair]bool);
  requires true;
  requires AllocatedXids[second_xid];
  requires pair(second_xid, second_mid, second_pair);
  requires xConsistent(state[second_xid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures true
     ==> (exists #tmp_0_second_newState: XState :: 
      AllocatedXids == old(AllocatedXids)[first_xid := true]
         && state == old(state)[second_xid := #tmp_0_second_newState]
         && first_xid == first_xid
         && first_pairs
           == (lambda first_p: Pair :: pair(first_xid, mid#Pair(first_p), first_p))
         && old(state)[second_xid := #tmp_0_second_newState][first_xid]
           == (lambda first_j: Mid :: UNDECIDED())
         && !old(AllocatedXids)[first_xid]
         && xConsistentExtension(old(state)[second_xid], #tmp_0_second_newState));



implementation GatePreservationChecker_atomic_Participant_VoteReq_10_atomic_AllocateXid_10(first_xid: Xid, first_mid: Mid, first_pair: Pair)
   returns (second_xid: Xid, second_pairs: [Pair]bool)
{

  second_anon0:
    assume !AllocatedXids[second_xid];
    assume state[second_xid] == (lambda second_j: Mid :: UNDECIDED());
    second_pairs := (lambda second_p: Pair :: pair(second_xid, mid#Pair(second_p), second_p));
    AllocatedXids[second_xid] := true;
    return;
}



procedure GatePreservationChecker_atomic_Participant_VoteReq_10_atomic_AllocateXid_10(first_xid: Xid, first_mid: Mid, first_pair: Pair)
   returns (second_xid: Xid, second_pairs: [Pair]bool);
  requires true;
  requires AllocatedXids[first_xid];
  requires pair(first_xid, first_mid, first_pair);
  requires xConsistent(state[first_xid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(PairCollector(first_pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(second_pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true))
     ==> AllocatedXids[first_xid];
  ensures (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(PairCollector(first_pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(second_pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true))
     ==> pair(first_xid, first_mid, first_pair);
  ensures (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(PairCollector(first_pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(second_pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true))
     ==> xConsistent(state[first_xid]);



implementation NonBlockingChecker_atomic_Participant_VoteReq_10(second_xid: Xid, second_mid: Mid, second_pair: Pair)
{

  L:
    assert (exists #tmp_0_second_newState: XState :: 
      xConsistentExtension(old(state)[second_xid], #tmp_0_second_newState));
    return;
}



procedure NonBlockingChecker_atomic_Participant_VoteReq_10(second_xid: Xid, second_mid: Mid, second_pair: Pair);
  requires true;
  requires AllocatedXids[second_xid];
  requires pair(second_xid, second_mid, second_pair);
  requires xConsistent(state[second_xid]);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure {:inline 1} skip_dummy_YieldInv_8();



implementation {:inline 1} skip_dummy_YieldInv_8()
{

  _init:
    return;
}



procedure {:inline 1} skip_dummy_YieldPairs_8(xid: Xid, pairs: [Pair]bool);



implementation {:inline 1} skip_dummy_YieldPairs_8(xid: Xid, pairs: [Pair]bool)
{

  _init:
    return;
}



procedure {:inline 1} skip_dummy_YieldUndecidedOrCommitted_8(xid: Xid, mid: Mid, pair: Pair);



implementation {:inline 1} skip_dummy_YieldUndecidedOrCommitted_8(xid: Xid, mid: Mid, pair: Pair)
{

  _init:
    return;
}



procedure {:inline 1} skip_dummy_YieldAborted_8(xid: Xid, mid: Mid, pair: Pair);



implementation {:inline 1} skip_dummy_YieldAborted_8(xid: Xid, mid: Mid, pair: Pair)
{

  _init:
    return;
}



procedure {:inline 1} skip_dummy_YieldInv_9(xid: Xid);



implementation {:inline 1} skip_dummy_YieldInv_9(xid: Xid)
{

  _init:
    return;
}



procedure {:inline 1} skip_dummy_YieldConsistent_9();



implementation {:inline 1} skip_dummy_YieldConsistent_9()
{

  _init:
    return;
}



procedure {:inline 1} skip_dummy_YieldConsistent_10();



implementation {:inline 1} skip_dummy_YieldConsistent_10()
{

  _init:
    return;
}



procedure {:inline 1} skip_dummy_YieldConsistent_11();



implementation {:inline 1} skip_dummy_YieldConsistent_11()
{

  _init:
    return;
}



procedure {:inline 1} skip_dummy_main();



implementation {:inline 1} skip_dummy_main()
{

  _init:
    return;
}



procedure YieldInv_8_7();
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure YieldPairs_8_7(xid: Xid, pairs: [Pair]bool);
  free requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairSetCollector(pairs), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure YieldUndecidedOrCommitted_8_7(xid: Xid, mid: Mid, pair: Pair);
  free requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure YieldAborted_8_7(xid: Xid, mid: Mid, pair: Pair);
  free requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure YieldInv_9_7(xid: Xid);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure YieldConsistent_9_7();
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure YieldConsistent_10_7();
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure YieldConsistent_11_7();
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure main_7();
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure Coordinator_TransactionReq_7() returns (xid: Xid);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure Participant_VoteReq_7(xid: Xid, mid: Mid, pair: Pair);
  free requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure Coordinator_VoteYes_7(xid: Xid, mid: Mid, pair: Pair);
  free requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure Coordinator_VoteNo_7(xid: Xid, mid: Mid, pair: Pair);
  free requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure SetParticipantAborted_7(xid: Xid, mid: Mid, pair: Pair);
  free requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure StateUpdateOnVoteYes_7(xid: Xid, mid: Mid) returns (commit: bool);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure StateUpdateOnVoteNo_7(xid: Xid, mid: Mid) returns (abort: bool);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure Participant_Commit_7(xid: Xid, mid: Mid);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure Participant_Abort_7(xid: Xid, mid: Mid);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure AllocateXid_7() returns (xid: Xid, pairs: [Pair]bool);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  free ensures (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairSetCollector(pairs), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));



procedure TransferPair_7(xid: Xid, mid: Mid, inPairs: [Pair]bool) returns (pairs: [Pair]bool, pair: Pair);
  free requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairSetCollector(inPairs), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  free ensures (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairSetCollector(pairs), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
         == linear_pair_MapConstBool(true));



implementation YieldInv_8_7()
{
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    yield;
    assert Inv_8(state, B, votes);
  **** end structured program */

  og_init:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon01, CallToYieldProc;

  anon05:
    return;

  anon01:
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon05, CallToYieldProc;

  CallToYieldProc:
    call og_yield_7(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation YieldPairs_8_7(xid: Xid, pairs: [Pair]bool)
{
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    yield;
    assert Inv_8(state, B, votes)
       && (votes[xid] == -1
         || (forall p: Pair :: 
          pairs[p]
             ==> pair(xid, mid#Pair(p), p) && UndecidedOrCommitted(state[xid][mid#Pair(p)])));
  **** end structured program */

  og_init:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairSetCollector(pairs), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon01, CallToYieldProc;

  anon05:
    return;

  anon01:
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairSetCollector(pairs), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon05, CallToYieldProc;

  CallToYieldProc:
    call og_yield_7(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation YieldUndecidedOrCommitted_8_7(xid: Xid, mid: Mid, pair: Pair)
{
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    yield;
    assert Inv_8(state, B, votes)
       && pair(xid, mid, pair)
       && (votes[xid] == -1 || UndecidedOrCommitted(state[xid][mid]));
  **** end structured program */

  og_init:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon01, CallToYieldProc;

  anon05:
    return;

  anon01:
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon05, CallToYieldProc;

  CallToYieldProc:
    call og_yield_7(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation YieldAborted_8_7(xid: Xid, mid: Mid, pair: Pair)
{
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    yield;
    assert Inv_8(state, B, votes) && pair(xid, mid, pair) && Aborted(state[xid][mid]);
  **** end structured program */

  og_init:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon01, CallToYieldProc;

  anon05:
    return;

  anon01:
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon05, CallToYieldProc;

  CallToYieldProc:
    call og_yield_7(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation YieldInv_9_7(xid: Xid)
{
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    yield;
    assert Inv_9(state, B, xid);
  **** end structured program */

  og_init:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon01, CallToYieldProc;

  anon05:
    return;

  anon01:
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon05, CallToYieldProc;

  CallToYieldProc:
    call og_yield_7(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation YieldConsistent_9_7()
{
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    yield;
    assert gConsistent(state);
  **** end structured program */

  og_init:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon01, CallToYieldProc;

  anon05:
    return;

  anon01:
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon05, CallToYieldProc;

  CallToYieldProc:
    call og_yield_7(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation YieldConsistent_10_7()
{
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    yield;
    assert gConsistent(state);
  **** end structured program */

  og_init:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon01, CallToYieldProc;

  anon05:
    return;

  anon01:
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon05, CallToYieldProc;

  CallToYieldProc:
    call og_yield_7(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation YieldConsistent_11_7()
{
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    yield;
    assert gConsistent(state);
  **** end structured program */

  og_init:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon01, CallToYieldProc;

  anon05:
    return;

  anon01:
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon05, CallToYieldProc;

  CallToYieldProc:
    call og_yield_7(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation main_7()
{
  var xid: Xid;
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    while (*)
      invariant Inv_8(state, B, votes);
      invariant gConsistent(state);
    {
        call xid := Coordinator_TransactionReq();
    }

    yield;
  **** end structured program */

  og_init:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon3_LoopHead:
    assume linear_pair_available == linear_pair_MapConstBool(false);
    assume state == og_global_old_state;
    assume votes == og_global_old_votes;
    assume B == og_global_old_B;
    assume AllocatedXids == og_global_old_AllocatedXids;
    assume pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon3_LoopDone, anon3_LoopBody;

  anon3_LoopBody:
    goto anon3_LoopBody0, CallToYieldProc;

  anon3_LoopDone:
    goto anon2;

  anon2:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon21, CallToYieldProc;

  anon04:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon3_LoopHead;

  anon00:
    call og_YieldInv_8_7_YieldConsistent_9_7_YieldConsistent_10_7_YieldConsistent_11_7();
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon04, CallToYieldProc;

  anon3_LoopBody8:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon3_LoopHead;

  anon3_LoopBody4:
    call og_YieldInv_8_7_YieldConsistent_9_7_YieldConsistent_10_7_YieldConsistent_11_7();
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon3_LoopBody8, CallToYieldProc;

  anon3_LoopBody0:
    call xid := Coordinator_TransactionReq_7();
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon3_LoopBody4, CallToYieldProc;

  anon25:
    return;

  anon21:
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon25, CallToYieldProc;

  CallToYieldProc:
    call og_yield_7(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation Coordinator_TransactionReq_7() returns (xid: Xid)
{
  var pair: Pair;
  var pairs: [Pair]bool;
  var snapshot: GState;
  var i: Mid;
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    call xid, pairs := AllocateXid();
    call snapshot := GhostRead();
    i := 1;
    while (i <= numParticipants)
      invariant {:terminates} true;
      invariant Inv_8(state, B, votes);
      invariant pairs == (lambda p: Pair :: pair(xid, mid#Pair(p), p) && i <= mid#Pair(p));
      invariant votes[xid] == -1
         || (forall p: Pair :: pairs[p] ==> UndecidedOrCommitted(state[xid][mid#Pair(p)]));
      invariant Inv_9(state, B, xid);
      invariant gConsistent(state);
      invariant ExistsMonotoneExtension(snapshot, state, xid);
      invariant 1 <= i && i <= numParticipants + 1;
    {
        call pairs, pair := TransferPair(xid, i, pairs);
        async call Participant_VoteReq(xid, i, pair);
        i := i + 1;
    }

  **** end structured program */

  og_init:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon3_LoopHead:
    assume linear_pair_available
       == linear_pair_MapOr(PairSetCollector(pairs), linear_pair_MapConstBool(false));
    assume state == og_global_old_state;
    assume votes == og_global_old_votes;
    assume B == og_global_old_B;
    assume AllocatedXids == og_global_old_AllocatedXids;
    assume pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon3_LoopDone, anon3_LoopBody;

  anon3_LoopBody:
    assume {:partition} i <= numParticipants;
    goto anon3_LoopBody1, CallToYieldProc;

  anon3_LoopDone:
    assume {:partition} numParticipants < i;
    goto anon2;

  anon2:
    goto anon20, CallToYieldProc;

  anon010:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairSetCollector(pairs), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon3_LoopHead;

  anon04:
    call xid, pairs := AllocateXid_7();
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairSetCollector(pairs), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    i := 1;
    goto anon010, CallToYieldProc;

  anon00:
    call og_YieldInv_8_7_YieldConsistent_9_7_YieldConsistent_10_7();
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon04, CallToYieldProc;

  anon3_LoopBody14:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairSetCollector(pairs), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon3_LoopHead;

  anon3_LoopBody10:
    call og_YieldPairs_8_7_YieldInv_9_7(xid, pairs, xid);
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairSetCollector(pairs), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon3_LoopBody14, CallToYieldProc;

  anon3_LoopBody5:
    call DummyAsyncTarget_Participant_VoteReq_7(xid, i, pair);
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairSetCollector(pairs), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    i := i + 1;
    goto anon3_LoopBody10, CallToYieldProc;

  anon3_LoopBody1:
    call pairs, pair := TransferPair_7(xid, i, pairs);
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairCollector(pair), 
      linear_pair_MapOr(PairSetCollector(pairs), linear_pair_MapConstBool(false))), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(3)))
           == linear_pair_MapConstBool(true));
    goto anon3_LoopBody5, CallToYieldProc;

  anon24:
    return;

  anon20:
    call og_YieldInv_8_7_YieldConsistent_9_7_YieldConsistent_10_7();
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairSetCollector(pairs), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon24, CallToYieldProc;

  CallToYieldProc:
    call og_yield_7(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation Participant_VoteReq_7(xid: Xid, mid: Mid, pair: Pair)
{
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    if (*)
    {
        async call Coordinator_VoteYes(xid, mid, pair);
    }
    else
    {
        call SetParticipantAborted(xid, mid, pair);
        async call Coordinator_VoteNo(xid, mid, pair);
    }

    yield;
  **** end structured program */

  og_init:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon4_Else:
    goto anon4_Else0, CallToYieldProc;

  anon3:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon31, CallToYieldProc;

  anon4_Then:
    goto anon4_Then0, CallToYieldProc;

  anon00:
    call og_YieldUndecidedOrCommitted_8_7_YieldInv_9_7(xid, mid, pair, xid);
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon4_Then, anon4_Else;

  anon4_Else4:
    call DummyAsyncTarget_Coordinator_VoteNo_7(xid, mid, pair);
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon3;

  anon4_Else0:
    call SetParticipantAborted_7(xid, mid, pair);
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon4_Else4, CallToYieldProc;

  anon35:
    return;

  anon31:
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon35, CallToYieldProc;

  anon4_Then0:
    call DummyAsyncTarget_Coordinator_VoteYes_7(xid, mid, pair);
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon3;

  CallToYieldProc:
    call og_yield_7(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation Coordinator_VoteYes_7(xid: Xid, mid: Mid, pair: Pair)
{
  var commit: bool;
  var i: Mid;
  var snapshot: GState;
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    call YieldUndecidedOrCommitted_8(xid, mid, pair);
    call snapshot := GhostRead();
    call Lemma_add_to_B(pair);
    call Lemma_all_in_B(xid);
    call commit := StateUpdateOnVoteYes(xid, mid);
    call Lemma_all_in_B(xid);
    if (commit)
    {
        assert xUndecidedOrCommitted(snapshot[xid]);
        assert xUndecidedOrCommitted(state[xid]);
        i := 1;
        while (i <= numParticipants)
          invariant {:terminates} true;
          invariant 1 <= i && i <= numParticipants + 1;
          invariant Inv_8(state, B, votes);
          invariant ExistsMonotoneExtension(snapshot, state, xid);
        {
            async call Participant_Commit(xid, i);
            i := i + 1;
        }
    }

    yield;
  **** end structured program */

  og_init:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon4_Else:
    assume {:partition} !commit;
    goto anon3;

  anon3:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon31, CallToYieldProc;

  anon4_Then:
    assume {:partition} commit;
    i := 1;
    goto anon4_Then2, CallToYieldProc;

  anon5_LoopHead:
    assume linear_pair_available
       == linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false));
    assume state == og_global_old_state;
    assume votes == og_global_old_votes;
    assume B == og_global_old_B;
    assume AllocatedXids == og_global_old_AllocatedXids;
    assume pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon5_LoopDone, anon5_LoopBody;

  anon5_LoopBody:
    assume {:partition} i <= numParticipants;
    goto anon5_LoopBody1, CallToYieldProc;

  anon5_LoopDone:
    assume {:partition} numParticipants < i;
    goto anon3;

  anon07:
    call commit := StateUpdateOnVoteYes_7(xid, mid);
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon4_Then, anon4_Else;

  anon00:
    call YieldUndecidedOrCommitted_8_7(xid, mid, pair);
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon07, CallToYieldProc;

  anon35:
    return;

  anon31:
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon35, CallToYieldProc;

  anon4_Then2:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon5_LoopHead;

  anon5_LoopBody6:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon5_LoopHead;

  anon5_LoopBody1:
    call DummyAsyncTarget_Participant_Commit_7(xid, i);
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    i := i + 1;
    goto anon5_LoopBody6, CallToYieldProc;

  CallToYieldProc:
    call og_yield_7(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation Coordinator_VoteNo_7(xid: Xid, mid: Mid, pair: Pair)
{
  var abort: bool;
  var i: int;
  var snapshot: GState;
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    call YieldAborted_8(xid, mid, pair);
    call snapshot := GhostRead();
    call abort := StateUpdateOnVoteNo(xid, mid);
    if (abort)
    {
        i := 1;
        while (i <= numParticipants)
          invariant {:terminates} true;
          invariant 1 <= i && i <= numParticipants + 1;
          invariant Aborted(state[xid][CoordinatorMid]);
          invariant xUndecidedOrAborted(state[xid]);
          invariant Inv_8(state, B, votes);
          invariant ExistsMonotoneExtension(snapshot, state, xid);
        {
            async call Participant_Abort(xid, i);
            i := i + 1;
        }
    }

    yield;
  **** end structured program */

  og_init:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon4_Else:
    assume {:partition} !abort;
    goto anon3;

  anon3:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon31, CallToYieldProc;

  anon4_Then:
    assume {:partition} abort;
    i := 1;
    goto anon4_Then2, CallToYieldProc;

  anon5_LoopHead:
    assume linear_pair_available
       == linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false));
    assume state == og_global_old_state;
    assume votes == og_global_old_votes;
    assume B == og_global_old_B;
    assume AllocatedXids == og_global_old_AllocatedXids;
    assume pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon5_LoopDone, anon5_LoopBody;

  anon5_LoopBody:
    assume {:partition} i <= numParticipants;
    goto anon5_LoopBody1, CallToYieldProc;

  anon5_LoopDone:
    assume {:partition} numParticipants < i;
    goto anon3;

  anon05:
    call abort := StateUpdateOnVoteNo_7(xid, mid);
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon4_Then, anon4_Else;

  anon00:
    call YieldAborted_8_7(xid, mid, pair);
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon05, CallToYieldProc;

  anon35:
    return;

  anon31:
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon35, CallToYieldProc;

  anon4_Then2:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon5_LoopHead;

  anon5_LoopBody6:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon5_LoopHead;

  anon5_LoopBody1:
    call DummyAsyncTarget_Participant_Abort_7(xid, i);
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    i := i + 1;
    goto anon5_LoopBody6, CallToYieldProc;

  CallToYieldProc:
    call og_yield_7(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



procedure {:inline 1} Impl_YieldChecker_YieldInv_8_7(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_YieldPairs_8_7(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_YieldUndecidedOrCommitted_8_7(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_YieldAborted_8_7(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_YieldInv_9_7(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_YieldConsistent_9_7(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_YieldConsistent_10_7(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_YieldConsistent_11_7(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_main_7(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_Participant_VoteReq_7(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_Coordinator_VoteYes_7(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_Coordinator_VoteNo_7(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



implementation {:inline 1} Impl_YieldChecker_YieldInv_8_7(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_YieldPairs_8_7(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var xid: Xid;
  var pairs: [Pair]bool;
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_YieldUndecidedOrCommitted_8_7(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var xid: Xid;
  var mid: Mid;
  var pair: Pair;
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_YieldAborted_8_7(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var xid: Xid;
  var mid: Mid;
  var pair: Pair;
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_YieldInv_9_7(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var xid: Xid;
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_YieldConsistent_9_7(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_YieldConsistent_10_7(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_YieldConsistent_11_7(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_main_7(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var xid: Xid;
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_Participant_VoteReq_7(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var xid: Xid;
  var mid: Mid;
  var pair: Pair;
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_Coordinator_VoteYes_7(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var commit: bool;
  var i: Mid;
  var snapshot: GState;
  var xid: Xid;
  var mid: Mid;
  var pair: Pair;
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_Coordinator_VoteNo_7(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var abort: bool;
  var i: int;
  var snapshot: GState;
  var xid: Xid;
  var mid: Mid;
  var pair: Pair;
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    assume false;
    return;
}



procedure og_YieldInv_8_7_YieldConsistent_9_7_YieldConsistent_10_7_YieldConsistent_11_7();
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure og_YieldInv_8_7_YieldConsistent_9_7_YieldConsistent_10_7();
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure DummyAsyncTarget_Participant_VoteReq_7(xid: Xid, mid: Mid, pair: Pair);
  free requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));



procedure og_YieldPairs_8_7_YieldInv_9_7(og_0_xid: Xid, og_0_pairs: [Pair]bool, og_1_xid: Xid);
  free requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairSetCollector(og_0_pairs), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure og_YieldUndecidedOrCommitted_8_7_YieldInv_9_7(og_0_xid: Xid, og_0_mid: Mid, og_0_pair: Pair, og_1_xid: Xid);
  free requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(og_0_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure DummyAsyncTarget_Coordinator_VoteNo_7(xid: Xid, mid: Mid, pair: Pair);
  free requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));



procedure DummyAsyncTarget_Coordinator_VoteYes_7(xid: Xid, mid: Mid, pair: Pair);
  free requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));



procedure DummyAsyncTarget_Participant_Commit_7(xid: Xid, mid: Mid);



procedure DummyAsyncTarget_Participant_Abort_7(xid: Xid, mid: Mid);



procedure {:inline 1} og_yield_7(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



implementation {:inline 1} og_yield_7(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{

  enter:
    goto L_0, L_1, L_2, L_3, L_4, L_5, L_6, L_7, L_8, L_9, L_10, L_11;

  L_0:
    call Impl_YieldChecker_YieldInv_8_7(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;

  L_1:
    call Impl_YieldChecker_YieldPairs_8_7(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;

  L_2:
    call Impl_YieldChecker_YieldUndecidedOrCommitted_8_7(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;

  L_3:
    call Impl_YieldChecker_YieldAborted_8_7(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;

  L_4:
    call Impl_YieldChecker_YieldInv_9_7(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;

  L_5:
    call Impl_YieldChecker_YieldConsistent_9_7(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;

  L_6:
    call Impl_YieldChecker_YieldConsistent_10_7(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;

  L_7:
    call Impl_YieldChecker_YieldConsistent_11_7(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;

  L_8:
    call Impl_YieldChecker_main_7(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;

  L_9:
    call Impl_YieldChecker_Participant_VoteReq_7(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;

  L_10:
    call Impl_YieldChecker_Coordinator_VoteYes_7(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;

  L_11:
    call Impl_YieldChecker_Coordinator_VoteNo_7(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;
}



procedure YieldInv_8_8();
  requires Inv_8(state, B, votes);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures Inv_8(state, B, votes);



procedure YieldPairs_8_8(xid: Xid, pairs: [Pair]bool);
  requires Inv_8(state, B, votes)
     && (votes[xid] == -1
       || (forall p: Pair :: 
        pairs[p]
           ==> pair(xid, mid#Pair(p), p) && UndecidedOrCommitted(state[xid][mid#Pair(p)])));
  free requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairSetCollector(pairs), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures Inv_8(state, B, votes)
     && (votes[xid] == -1
       || (forall p: Pair :: 
        pairs[p]
           ==> pair(xid, mid#Pair(p), p) && UndecidedOrCommitted(state[xid][mid#Pair(p)])));



procedure YieldUndecidedOrCommitted_8_8(xid: Xid, mid: Mid, pair: Pair);
  requires Inv_8(state, B, votes)
     && pair(xid, mid, pair)
     && (votes[xid] == -1 || UndecidedOrCommitted(state[xid][mid]));
  free requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures Inv_8(state, B, votes)
     && pair(xid, mid, pair)
     && (votes[xid] == -1 || UndecidedOrCommitted(state[xid][mid]));



procedure YieldAborted_8_8(xid: Xid, mid: Mid, pair: Pair);
  requires Inv_8(state, B, votes) && pair(xid, mid, pair) && Aborted(state[xid][mid]);
  free requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures Inv_8(state, B, votes) && pair(xid, mid, pair) && Aborted(state[xid][mid]);



procedure YieldInv_9_8(xid: Xid);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure YieldConsistent_9_8();
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure YieldConsistent_10_8();
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure YieldConsistent_11_8();
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure main_8();
  requires gUndecided(state);
  requires votes == (lambda xid: Xid :: 0);
  requires B == (lambda p: Pair :: false);
  requires (forall B: [Pair]bool, xid: Xid :: card(B, xid) == 0);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure Coordinator_TransactionReq_8() returns (xid: Xid);
  requires Inv_8(state, B, votes);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures Inv_8(state, B, votes);



procedure Participant_VoteReq_8(xid: Xid, mid: Mid, pair: Pair);
  requires Inv_8(state, B, votes)
     && pair(xid, mid, pair)
     && (votes[xid] == -1 || UndecidedOrCommitted(state[xid][mid]));
  free requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure Coordinator_VoteYes_8(xid: Xid, mid: Mid, pair: Pair);
  requires Inv_8(state, B, votes)
     && pair(xid, mid, pair)
     && (votes[xid] == -1 || UndecidedOrCommitted(state[xid][mid]));
  free requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure Coordinator_VoteNo_8(xid: Xid, mid: Mid, pair: Pair);
  requires Inv_8(state, B, votes) && pair(xid, mid, pair) && Aborted(state[xid][mid]);
  free requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



implementation YieldInv_8_8()
{
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    yield;
    assert Inv_8(state, B, votes);
  **** end structured program */

  og_init:
    og_pc, og_ok, linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := false, false, linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assert Inv_8(state, B, votes);
    goto anon02, CallToYieldProc;

  anon011:
    assert og_pc
       || 
      (
        state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (
        state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_pc
       ==> state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (
        state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_ok;
    return;

  anon02:
    assert og_pc
       || 
      (
        state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (
        state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_pc
       ==> state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (
        state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume true;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assume Inv_8(state, B, votes);
    goto anon011, CallToYieldProc;

  CallToYieldProc:
    call og_yield_8(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation YieldPairs_8_8(xid: Xid, pairs: [Pair]bool)
{
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    yield;
    assert Inv_8(state, B, votes)
       && (votes[xid] == -1
         || (forall p: Pair :: 
          pairs[p]
             ==> pair(xid, mid#Pair(p), p) && UndecidedOrCommitted(state[xid][mid#Pair(p)])));
  **** end structured program */

  og_init:
    og_pc, og_ok, linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := false, false, linear_pair_MapOr(PairSetCollector(pairs), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    assert Inv_8(state, B, votes)
       && (votes[xid] == -1
         || (forall p: Pair :: 
          pairs[p]
             ==> pair(xid, mid#Pair(p), p) && UndecidedOrCommitted(state[xid][mid#Pair(p)])));
    goto anon02, CallToYieldProc;

  anon011:
    assert og_pc
       || 
      (
        state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (
        state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_pc
       ==> state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (
        state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_ok;
    return;

  anon02:
    assert og_pc
       || 
      (
        state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (
        state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_pc
       ==> state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (
        state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume true;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairSetCollector(pairs), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    assume Inv_8(state, B, votes)
       && (votes[xid] == -1
         || (forall p: Pair :: 
          pairs[p]
             ==> pair(xid, mid#Pair(p), p) && UndecidedOrCommitted(state[xid][mid#Pair(p)])));
    goto anon011, CallToYieldProc;

  CallToYieldProc:
    call og_yield_8(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation YieldUndecidedOrCommitted_8_8(xid: Xid, mid: Mid, pair: Pair)
{
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    yield;
    assert Inv_8(state, B, votes)
       && pair(xid, mid, pair)
       && (votes[xid] == -1 || UndecidedOrCommitted(state[xid][mid]));
  **** end structured program */

  og_init:
    og_pc, og_ok, linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := false, false, linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    assert Inv_8(state, B, votes)
       && pair(xid, mid, pair)
       && (votes[xid] == -1 || UndecidedOrCommitted(state[xid][mid]));
    goto anon02, CallToYieldProc;

  anon011:
    assert og_pc
       || 
      (
        state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (
        state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_pc
       ==> state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (
        state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_ok;
    return;

  anon02:
    assert og_pc
       || 
      (
        state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (
        state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_pc
       ==> state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (
        state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume true;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    assume Inv_8(state, B, votes)
       && pair(xid, mid, pair)
       && (votes[xid] == -1 || UndecidedOrCommitted(state[xid][mid]));
    goto anon011, CallToYieldProc;

  CallToYieldProc:
    call og_yield_8(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation YieldAborted_8_8(xid: Xid, mid: Mid, pair: Pair)
{
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    yield;
    assert Inv_8(state, B, votes) && pair(xid, mid, pair) && Aborted(state[xid][mid]);
  **** end structured program */

  og_init:
    og_pc, og_ok, linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := false, false, linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    assert Inv_8(state, B, votes) && pair(xid, mid, pair) && Aborted(state[xid][mid]);
    goto anon02, CallToYieldProc;

  anon011:
    assert og_pc
       || 
      (
        state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (
        state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_pc
       ==> state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (
        state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_ok;
    return;

  anon02:
    assert og_pc
       || 
      (
        state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (
        state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_pc
       ==> state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (
        state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume true;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    assume Inv_8(state, B, votes) && pair(xid, mid, pair) && Aborted(state[xid][mid]);
    goto anon011, CallToYieldProc;

  CallToYieldProc:
    call og_yield_8(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation YieldInv_9_8(xid: Xid)
{
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    yield;
    assert Inv_9(state, B, xid);
  **** end structured program */

  og_init:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon01, CallToYieldProc;

  anon05:
    return;

  anon01:
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon05, CallToYieldProc;

  CallToYieldProc:
    call og_yield_8(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation YieldConsistent_9_8()
{
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    yield;
    assert gConsistent(state);
  **** end structured program */

  og_init:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon01, CallToYieldProc;

  anon05:
    return;

  anon01:
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon05, CallToYieldProc;

  CallToYieldProc:
    call og_yield_8(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation YieldConsistent_10_8()
{
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    yield;
    assert gConsistent(state);
  **** end structured program */

  og_init:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon01, CallToYieldProc;

  anon05:
    return;

  anon01:
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon05, CallToYieldProc;

  CallToYieldProc:
    call og_yield_8(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation YieldConsistent_11_8()
{
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    yield;
    assert gConsistent(state);
  **** end structured program */

  og_init:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon01, CallToYieldProc;

  anon05:
    return;

  anon01:
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon05, CallToYieldProc;

  CallToYieldProc:
    call og_yield_8(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation main_8()
{
  var xid: Xid;
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    while (*)
      invariant Inv_8(state, B, votes);
      invariant gConsistent(state);
    {
        call xid := Coordinator_TransactionReq();
    }

    yield;
  **** end structured program */

  og_init:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon3_LoopHead:
    assume linear_pair_available == linear_pair_MapConstBool(false);
    assume state == og_global_old_state;
    assume votes == og_global_old_votes;
    assume B == og_global_old_B;
    assume AllocatedXids == og_global_old_AllocatedXids;
    assume pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assert Inv_8(state, B, votes);
    goto anon3_LoopDone, anon3_LoopBody;

  anon3_LoopBody:
    goto anon3_LoopBody0, CallToYieldProc;

  anon3_LoopDone:
    goto anon2;

  anon2:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon21, CallToYieldProc;

  anon04:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon3_LoopHead;

  anon00:
    call og_YieldInv_8_8_YieldConsistent_9_8_YieldConsistent_10_8_YieldConsistent_11_8();
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon04, CallToYieldProc;

  anon3_LoopBody8:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon3_LoopHead;

  anon3_LoopBody4:
    call og_YieldInv_8_8_YieldConsistent_9_8_YieldConsistent_10_8_YieldConsistent_11_8();
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon3_LoopBody8, CallToYieldProc;

  anon3_LoopBody0:
    call xid := Coordinator_TransactionReq_8();
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon3_LoopBody4, CallToYieldProc;

  anon25:
    return;

  anon21:
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon25, CallToYieldProc;

  CallToYieldProc:
    call og_yield_8(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation Coordinator_TransactionReq_8() returns (xid: Xid)
{
  var pair: Pair;
  var pairs: [Pair]bool;
  var snapshot: GState;
  var i: Mid;
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    call xid, pairs := AllocateXid();
    call snapshot := GhostRead();
    i := 1;
    while (i <= numParticipants)
      invariant {:terminates} true;
      invariant Inv_8(state, B, votes);
      invariant pairs == (lambda p: Pair :: pair(xid, mid#Pair(p), p) && i <= mid#Pair(p));
      invariant votes[xid] == -1
         || (forall p: Pair :: pairs[p] ==> UndecidedOrCommitted(state[xid][mid#Pair(p)]));
      invariant Inv_9(state, B, xid);
      invariant gConsistent(state);
      invariant ExistsMonotoneExtension(snapshot, state, xid);
      invariant 1 <= i && i <= numParticipants + 1;
    {
        call pairs, pair := TransferPair(xid, i, pairs);
        async call Participant_VoteReq(xid, i, pair);
        i := i + 1;
    }

  **** end structured program */

  og_init:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon3_LoopHead:
    assume linear_pair_available
       == linear_pair_MapOr(PairSetCollector(pairs), linear_pair_MapConstBool(false));
    assume state == og_global_old_state;
    assume votes == og_global_old_votes;
    assume B == og_global_old_B;
    assume AllocatedXids == og_global_old_AllocatedXids;
    assume pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    assert Inv_8(state, B, votes);
    assert pairs == (lambda p: Pair :: pair(xid, mid#Pair(p), p) && i <= mid#Pair(p));
    assert votes[xid] == -1
       || (forall p: Pair :: pairs[p] ==> UndecidedOrCommitted(state[xid][mid#Pair(p)]));
    assert 1 <= i && i <= numParticipants + 1;
    goto anon3_LoopDone, anon3_LoopBody;

  anon3_LoopBody:
    assume {:partition} i <= numParticipants;
    call pairs, pair := atomic_TransferPair_8(xid, i, pairs);
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(3)))
           == linear_pair_MapConstBool(true));
    goto anon3_LoopBody3, CallToYieldProc;

  anon3_LoopDone:
    assume {:partition} numParticipants < i;
    goto anon2;

  anon2:
    goto anon20, CallToYieldProc;

  anon08:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairSetCollector(pairs), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon3_LoopHead;

  anon00:
    call og_YieldInv_8_8_YieldConsistent_9_8_YieldConsistent_10_8();
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    call xid, pairs := atomic_AllocateXid_8();
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    i := 1;
    goto anon08, CallToYieldProc;

  anon3_LoopBody12:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairSetCollector(pairs), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon3_LoopHead;

  anon3_LoopBody8:
    call og_YieldPairs_8_8_YieldInv_9_8(xid, pairs, xid);
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairSetCollector(pairs), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon3_LoopBody12, CallToYieldProc;

  anon3_LoopBody3:
    call DummyAsyncTarget_Participant_VoteReq_8(xid, i, pair);
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairSetCollector(pairs), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    i := i + 1;
    goto anon3_LoopBody8, CallToYieldProc;

  anon24:
    return;

  anon20:
    call og_YieldInv_8_8_YieldConsistent_9_8_YieldConsistent_10_8();
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairSetCollector(pairs), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon24, CallToYieldProc;

  CallToYieldProc:
    call og_yield_8(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation Participant_VoteReq_8(xid: Xid, mid: Mid, pair: Pair)
{
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    if (*)
    {
        async call Coordinator_VoteYes(xid, mid, pair);
    }
    else
    {
        call SetParticipantAborted(xid, mid, pair);
        async call Coordinator_VoteNo(xid, mid, pair);
    }

    yield;
  **** end structured program */

  og_init:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon4_Else:
    // <<< injected gate
    assume pair(xid, mid, pair);
    assume xUndecidedOrAborted(state[xid]);
    // injected gate >>>
    call atomic_SetParticipantAborted_8(xid, mid, pair);
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon4_Else6, CallToYieldProc;

  anon3:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon31, CallToYieldProc;

  anon4_Then:
    goto anon4_Then0, CallToYieldProc;

  anon00:
    call og_YieldUndecidedOrCommitted_8_8_YieldInv_9_8(xid, mid, pair, xid);
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon4_Then, anon4_Else;

  anon4_Else6:
    call DummyAsyncTarget_Coordinator_VoteNo_8(xid, mid, pair);
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon3;

  anon35:
    return;

  anon31:
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon35, CallToYieldProc;

  anon4_Then0:
    call DummyAsyncTarget_Coordinator_VoteYes_8(xid, mid, pair);
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon3;

  CallToYieldProc:
    call og_yield_8(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation Coordinator_VoteYes_8(xid: Xid, mid: Mid, pair: Pair)
{
  var commit: bool;
  var i: Mid;
  var snapshot: GState;
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    call YieldUndecidedOrCommitted_8(xid, mid, pair);
    call snapshot := GhostRead();
    call Lemma_add_to_B(pair);
    call Lemma_all_in_B(xid);
    call commit := StateUpdateOnVoteYes(xid, mid);
    call Lemma_all_in_B(xid);
    if (commit)
    {
        assert xUndecidedOrCommitted(snapshot[xid]);
        assert xUndecidedOrCommitted(state[xid]);
        i := 1;
        while (i <= numParticipants)
          invariant {:terminates} true;
          invariant 1 <= i && i <= numParticipants + 1;
          invariant Inv_8(state, B, votes);
          invariant ExistsMonotoneExtension(snapshot, state, xid);
        {
            async call Participant_Commit(xid, i);
            i := i + 1;
        }
    }

    yield;
  **** end structured program */

  og_init:
    og_pc, og_ok, linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := false, false, linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon4_Else:
    assume {:partition} !commit;
    goto anon3;

  anon3:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon31, CallToYieldProc;

  anon4_Then:
    assume {:partition} commit;
    assert xUndecidedOrCommitted(snapshot[xid]);
    assert xUndecidedOrCommitted(state[xid]);
    i := 1;
    goto anon5_LoopHead;

  anon5_LoopHead:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    assert 1 <= i && i <= numParticipants + 1;
    assert Inv_8(state, B, votes);
    assert ExistsMonotoneExtension(snapshot, state, xid);
    goto anon5_LoopDone, anon5_LoopBody;

  anon5_LoopBody:
    assume {:partition} i <= numParticipants;
    // <<< injected gate
    assert participantMid(i);
    assert xUndecidedOrCommitted(state[xid]);
    assert Committed(state[xid][CoordinatorMid]);
    // injected gate >>>
    call atomic_Participant_Commit_8(xid, i);
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    i := i + 1;
    goto anon5_LoopHead;

  anon5_LoopDone:
    assume {:partition} numParticipants < i;
    goto anon3;

  anon00:
    assert og_pc
       || 
      (
        state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_newState: XState :: 
        state == og_global_old_state[xid := #tmp_0_second_newState]
           && B == og_global_old_B[pair := true]
           && AllocatedXids == og_global_old_AllocatedXids
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && xConsistentExtension(og_global_old_state[xid], #tmp_0_second_newState)
           && xAllParticipantsInB(xid, og_global_old_B[pair := true]))
       || (
        state == og_global_old_state
         && B == og_global_old_B[pair := true]
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_pc
       ==> state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_newState: XState :: 
        state == og_global_old_state[xid := #tmp_0_second_newState]
           && B == og_global_old_B[pair := true]
           && AllocatedXids == og_global_old_AllocatedXids
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && xConsistentExtension(og_global_old_state[xid], #tmp_0_second_newState)
           && xAllParticipantsInB(xid, og_global_old_B[pair := true]))
       || (
        state == og_global_old_state
         && B == og_global_old_B[pair := true]
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    call YieldUndecidedOrCommitted_8_8(xid, mid, pair);
    assume og_pc || (AllocatedXids[xid] && pair(xid, mid, pair) && xConsistent(state[xid]));
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    call snapshot := GhostRead();
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    call Lemma_add_to_B(pair);
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    call Lemma_all_in_B(xid);
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    // <<< injected gate
    assert AllocatedXids[xid];
    assert VotesEqCoordinatorState(votes, state, xid);
    // injected gate >>>
    call commit := atomic_StateUpdateOnVoteYes_8(xid, mid);
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    call Lemma_all_in_B(xid);
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon4_Then, anon4_Else;

  anon39:
    assert og_pc
       || 
      (
        state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_newState: XState :: 
        state == og_global_old_state[xid := #tmp_0_second_newState]
           && B == og_global_old_B[pair := true]
           && AllocatedXids == og_global_old_AllocatedXids
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && xConsistentExtension(og_global_old_state[xid], #tmp_0_second_newState)
           && xAllParticipantsInB(xid, og_global_old_B[pair := true]))
       || (
        state == og_global_old_state
         && B == og_global_old_B[pair := true]
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_pc
       ==> state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_newState: XState :: 
        state == og_global_old_state[xid := #tmp_0_second_newState]
           && B == og_global_old_B[pair := true]
           && AllocatedXids == og_global_old_AllocatedXids
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && xConsistentExtension(og_global_old_state[xid], #tmp_0_second_newState)
           && xAllParticipantsInB(xid, og_global_old_B[pair := true]))
       || (
        state == og_global_old_state
         && B == og_global_old_B[pair := true]
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_ok;
    return;

  anon31:
    assert og_pc
       || 
      (
        state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || 
      (exists #tmp_0_second_newState: XState :: 
        state == og_global_old_state[xid := #tmp_0_second_newState]
           && B == og_global_old_B[pair := true]
           && AllocatedXids == og_global_old_AllocatedXids
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && xConsistentExtension(og_global_old_state[xid], #tmp_0_second_newState)
           && xAllParticipantsInB(xid, og_global_old_B[pair := true]))
       || (
        state == og_global_old_state
         && B == og_global_old_B[pair := true]
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_pc
       ==> state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || 
      (exists #tmp_0_second_newState: XState :: 
        state == og_global_old_state[xid := #tmp_0_second_newState]
           && B == og_global_old_B[pair := true]
           && AllocatedXids == og_global_old_AllocatedXids
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && xConsistentExtension(og_global_old_state[xid], #tmp_0_second_newState)
           && xAllParticipantsInB(xid, og_global_old_B[pair := true]))
       || (
        state == og_global_old_state
         && B == og_global_old_B[pair := true]
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume og_pc || (AllocatedXids[xid] && pair(xid, mid, pair) && xConsistent(state[xid]));
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon39, CallToYieldProc;

  CallToYieldProc:
    call og_yield_8(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation Coordinator_VoteNo_8(xid: Xid, mid: Mid, pair: Pair)
{
  var abort: bool;
  var i: int;
  var snapshot: GState;
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    call YieldAborted_8(xid, mid, pair);
    call snapshot := GhostRead();
    call abort := StateUpdateOnVoteNo(xid, mid);
    if (abort)
    {
        i := 1;
        while (i <= numParticipants)
          invariant {:terminates} true;
          invariant 1 <= i && i <= numParticipants + 1;
          invariant Aborted(state[xid][CoordinatorMid]);
          invariant xUndecidedOrAborted(state[xid]);
          invariant Inv_8(state, B, votes);
          invariant ExistsMonotoneExtension(snapshot, state, xid);
        {
            async call Participant_Abort(xid, i);
            i := i + 1;
        }
    }

    yield;
  **** end structured program */

  og_init:
    og_pc, og_ok, linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := false, false, linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon4_Else:
    assume {:partition} !abort;
    goto anon3;

  anon3:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon31, CallToYieldProc;

  anon4_Then:
    assume {:partition} abort;
    i := 1;
    goto anon5_LoopHead;

  anon5_LoopHead:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    assert 1 <= i && i <= numParticipants + 1;
    assert Aborted(state[xid][CoordinatorMid]);
    assert xUndecidedOrAborted(state[xid]);
    assert Inv_8(state, B, votes);
    assert ExistsMonotoneExtension(snapshot, state, xid);
    goto anon5_LoopDone, anon5_LoopBody;

  anon5_LoopBody:
    assume {:partition} i <= numParticipants;
    // <<< injected gate
    assert participantMid(i);
    assert xUndecidedOrAborted(state[xid]);
    assert Aborted(state[xid][CoordinatorMid]);
    // injected gate >>>
    call atomic_Participant_Abort_8(xid, i);
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    i := i + 1;
    goto anon5_LoopHead;

  anon5_LoopDone:
    assume {:partition} numParticipants < i;
    goto anon3;

  anon00:
    assert og_pc
       || 
      (
        state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (exists #tmp_0_second_newState: XState :: 
        state == og_global_old_state[xid := #tmp_0_second_newState]
           && B == og_global_old_B
           && AllocatedXids == og_global_old_AllocatedXids
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && xConsistentExtension(og_global_old_state[xid], #tmp_0_second_newState)
           && xUndecidedOrAborted(#tmp_0_second_newState));
    assert og_pc
       ==> state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (exists #tmp_0_second_newState: XState :: 
        state == og_global_old_state[xid := #tmp_0_second_newState]
           && B == og_global_old_B
           && AllocatedXids == og_global_old_AllocatedXids
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && xConsistentExtension(og_global_old_state[xid], #tmp_0_second_newState)
           && xUndecidedOrAborted(#tmp_0_second_newState));
    call YieldAborted_8_8(xid, mid, pair);
    assume og_pc
       || (AllocatedXids[xid] && pair(xid, mid, pair) && xUndecidedOrAborted(state[xid]));
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    call snapshot := GhostRead();
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    // <<< injected gate
    assert AllocatedXids[xid];
    assert !Committed(state[xid][CoordinatorMid]);
    // injected gate >>>
    call abort := atomic_StateUpdateOnVoteNo_8(xid, mid);
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon4_Then, anon4_Else;

  anon39:
    assert og_pc
       || 
      (
        state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (exists #tmp_0_second_newState: XState :: 
        state == og_global_old_state[xid := #tmp_0_second_newState]
           && B == og_global_old_B
           && AllocatedXids == og_global_old_AllocatedXids
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && xConsistentExtension(og_global_old_state[xid], #tmp_0_second_newState)
           && xUndecidedOrAborted(#tmp_0_second_newState));
    assert og_pc
       ==> state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (exists #tmp_0_second_newState: XState :: 
        state == og_global_old_state[xid := #tmp_0_second_newState]
           && B == og_global_old_B
           && AllocatedXids == og_global_old_AllocatedXids
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && xConsistentExtension(og_global_old_state[xid], #tmp_0_second_newState)
           && xUndecidedOrAborted(#tmp_0_second_newState));
    assert og_ok;
    return;

  anon31:
    assert og_pc
       || 
      (
        state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (exists #tmp_0_second_newState: XState :: 
        state == og_global_old_state[xid := #tmp_0_second_newState]
           && B == og_global_old_B
           && AllocatedXids == og_global_old_AllocatedXids
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && xConsistentExtension(og_global_old_state[xid], #tmp_0_second_newState)
           && xUndecidedOrAborted(#tmp_0_second_newState));
    assert og_pc
       ==> state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := state == og_global_old_state
         && B == og_global_old_B
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (exists #tmp_0_second_newState: XState :: 
        state == og_global_old_state[xid := #tmp_0_second_newState]
           && B == og_global_old_B
           && AllocatedXids == og_global_old_AllocatedXids
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && xConsistentExtension(og_global_old_state[xid], #tmp_0_second_newState)
           && xUndecidedOrAborted(#tmp_0_second_newState));
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume og_pc
       || (AllocatedXids[xid] && pair(xid, mid, pair) && xUndecidedOrAborted(state[xid]));
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon39, CallToYieldProc;

  CallToYieldProc:
    call og_yield_8(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



procedure {:inline 1} Impl_YieldChecker_YieldInv_8_8(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_YieldPairs_8_8(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_YieldUndecidedOrCommitted_8_8(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_YieldAborted_8_8(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_YieldInv_9_8(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_YieldConsistent_9_8(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_YieldConsistent_10_8(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_YieldConsistent_11_8(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_main_8(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_Participant_VoteReq_8(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_Coordinator_VoteYes_8(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_Coordinator_VoteNo_8(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



implementation {:inline 1} Impl_YieldChecker_YieldInv_8_8(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assume Inv_8(og_global_old_state, og_global_old_B, og_global_old_votes);
    assert Inv_8(state, B, votes);
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_YieldPairs_8_8(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var xid: Xid;
  var pairs: [Pair]bool;
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    assume Inv_8(og_global_old_state, og_global_old_B, og_global_old_votes)
       && (og_global_old_votes[xid] == -1
         || (forall p: Pair :: 
          pairs[p]
             ==> pair(xid, mid#Pair(p), p)
               && UndecidedOrCommitted(og_global_old_state[xid][mid#Pair(p)])));
    assert Inv_8(state, B, votes)
       && (votes[xid] == -1
         || (forall p: Pair :: 
          pairs[p]
             ==> pair(xid, mid#Pair(p), p) && UndecidedOrCommitted(state[xid][mid#Pair(p)])));
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_YieldUndecidedOrCommitted_8_8(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var xid: Xid;
  var mid: Mid;
  var pair: Pair;
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    assume Inv_8(og_global_old_state, og_global_old_B, og_global_old_votes)
       && pair(xid, mid, pair)
       && (og_global_old_votes[xid] == -1
         || UndecidedOrCommitted(og_global_old_state[xid][mid]));
    assert Inv_8(state, B, votes)
       && pair(xid, mid, pair)
       && (votes[xid] == -1 || UndecidedOrCommitted(state[xid][mid]));
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_YieldAborted_8_8(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var xid: Xid;
  var mid: Mid;
  var pair: Pair;
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    assume Inv_8(og_global_old_state, og_global_old_B, og_global_old_votes)
       && pair(xid, mid, pair)
       && Aborted(og_global_old_state[xid][mid]);
    assert Inv_8(state, B, votes) && pair(xid, mid, pair) && Aborted(state[xid][mid]);
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_YieldInv_9_8(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var xid: Xid;
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_YieldConsistent_9_8(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_YieldConsistent_10_8(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_YieldConsistent_11_8(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_main_8(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var xid: Xid;
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_Participant_VoteReq_8(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var xid: Xid;
  var mid: Mid;
  var pair: Pair;
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_Coordinator_VoteYes_8(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var commit: bool;
  var i: Mid;
  var snapshot: GState;
  var xid: Xid;
  var mid: Mid;
  var pair: Pair;
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_Coordinator_VoteNo_8(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var abort: bool;
  var i: int;
  var snapshot: GState;
  var xid: Xid;
  var mid: Mid;
  var pair: Pair;
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    assume false;
    return;
}



procedure og_YieldInv_8_8_YieldConsistent_9_8_YieldConsistent_10_8_YieldConsistent_11_8();
  requires Inv_8(state, B, votes);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures Inv_8(state, B, votes);



procedure og_YieldInv_8_8_YieldConsistent_9_8_YieldConsistent_10_8();
  requires Inv_8(state, B, votes);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures Inv_8(state, B, votes);



procedure DummyAsyncTarget_Participant_VoteReq_8(xid: Xid, mid: Mid, pair: Pair);
  requires Inv_8(state, B, votes)
     && pair(xid, mid, pair)
     && (votes[xid] == -1 || UndecidedOrCommitted(state[xid][mid]));
  free requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));



procedure og_YieldPairs_8_8_YieldInv_9_8(og_0_xid: Xid, og_0_pairs: [Pair]bool, og_1_xid: Xid);
  requires Inv_8(state, B, votes)
     && (votes[og_0_xid] == -1
       || (forall p: Pair :: 
        og_0_pairs[p]
           ==> pair(og_0_xid, mid#Pair(p), p)
             && UndecidedOrCommitted(state[og_0_xid][mid#Pair(p)])));
  free requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairSetCollector(og_0_pairs), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures Inv_8(state, B, votes)
     && (votes[og_0_xid] == -1
       || (forall p: Pair :: 
        og_0_pairs[p]
           ==> pair(og_0_xid, mid#Pair(p), p)
             && UndecidedOrCommitted(state[og_0_xid][mid#Pair(p)])));



procedure og_YieldUndecidedOrCommitted_8_8_YieldInv_9_8(og_0_xid: Xid, og_0_mid: Mid, og_0_pair: Pair, og_1_xid: Xid);
  requires Inv_8(state, B, votes)
     && pair(og_0_xid, og_0_mid, og_0_pair)
     && (votes[og_0_xid] == -1 || UndecidedOrCommitted(state[og_0_xid][og_0_mid]));
  free requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(og_0_pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures Inv_8(state, B, votes)
     && pair(og_0_xid, og_0_mid, og_0_pair)
     && (votes[og_0_xid] == -1 || UndecidedOrCommitted(state[og_0_xid][og_0_mid]));



procedure DummyAsyncTarget_Coordinator_VoteNo_8(xid: Xid, mid: Mid, pair: Pair);
  requires Inv_8(state, B, votes) && pair(xid, mid, pair) && Aborted(state[xid][mid]);
  free requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));



procedure DummyAsyncTarget_Coordinator_VoteYes_8(xid: Xid, mid: Mid, pair: Pair);
  requires Inv_8(state, B, votes)
     && pair(xid, mid, pair)
     && (votes[xid] == -1 || UndecidedOrCommitted(state[xid][mid]));
  free requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));



procedure {:inline 1} og_yield_8(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



implementation {:inline 1} og_yield_8(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{

  enter:
    goto L_0, L_1, L_2, L_3, L_4, L_5, L_6, L_7, L_8, L_9, L_10, L_11;

  L_0:
    call Impl_YieldChecker_YieldInv_8_8(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;

  L_1:
    call Impl_YieldChecker_YieldPairs_8_8(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;

  L_2:
    call Impl_YieldChecker_YieldUndecidedOrCommitted_8_8(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;

  L_3:
    call Impl_YieldChecker_YieldAborted_8_8(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;

  L_4:
    call Impl_YieldChecker_YieldInv_9_8(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;

  L_5:
    call Impl_YieldChecker_YieldConsistent_9_8(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;

  L_6:
    call Impl_YieldChecker_YieldConsistent_10_8(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;

  L_7:
    call Impl_YieldChecker_YieldConsistent_11_8(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;

  L_8:
    call Impl_YieldChecker_main_8(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;

  L_9:
    call Impl_YieldChecker_Participant_VoteReq_8(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;

  L_10:
    call Impl_YieldChecker_Coordinator_VoteYes_8(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;

  L_11:
    call Impl_YieldChecker_Coordinator_VoteNo_8(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;
}



procedure YieldInv_9_9(xid: Xid);
  requires Inv_9(state, B, xid);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures Inv_9(state, B, xid);



procedure YieldConsistent_9_9();
  requires gConsistent(state);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures gConsistent(state);



procedure YieldConsistent_10_9();
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure YieldConsistent_11_9();
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure main_9();
  requires gUndecided(state);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure Coordinator_TransactionReq_9() returns (xid: Xid);
  requires gConsistent(state);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures gConsistent(state);



procedure Participant_VoteReq_9(xid: Xid, mid: Mid, pair: Pair);
  requires Inv_9(state, B, xid);
  free requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



implementation YieldInv_9_9(xid: Xid)
{
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    yield;
    assert Inv_9(state, B, xid);
  **** end structured program */

  og_init:
    og_pc, og_ok, linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := false, false, linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assert Inv_9(state, B, xid);
    goto anon02, CallToYieldProc;

  anon011:
    assert og_pc
       || 
      (
        state == og_global_old_state
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (
        state == og_global_old_state
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_pc
       ==> state == og_global_old_state
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := state == og_global_old_state
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (
        state == og_global_old_state
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_ok;
    return;

  anon02:
    assert og_pc
       || 
      (
        state == og_global_old_state
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (
        state == og_global_old_state
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_pc
       ==> state == og_global_old_state
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := state == og_global_old_state
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (
        state == og_global_old_state
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume true;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assume Inv_9(state, B, xid);
    goto anon011, CallToYieldProc;

  CallToYieldProc:
    call og_yield_9(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation YieldConsistent_9_9()
{
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    yield;
    assert gConsistent(state);
  **** end structured program */

  og_init:
    og_pc, og_ok, linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := false, false, linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assert gConsistent(state);
    goto anon02, CallToYieldProc;

  anon011:
    assert og_pc
       || 
      (
        state == og_global_old_state
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (
        state == og_global_old_state
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_pc
       ==> state == og_global_old_state
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := state == og_global_old_state
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (
        state == og_global_old_state
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_ok;
    return;

  anon02:
    assert og_pc
       || 
      (
        state == og_global_old_state
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (
        state == og_global_old_state
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_pc
       ==> state == og_global_old_state
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := state == og_global_old_state
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (
        state == og_global_old_state
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume true;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assume gConsistent(state);
    goto anon011, CallToYieldProc;

  CallToYieldProc:
    call og_yield_9(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation YieldConsistent_10_9()
{
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    yield;
    assert gConsistent(state);
  **** end structured program */

  og_init:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon01, CallToYieldProc;

  anon05:
    return;

  anon01:
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon05, CallToYieldProc;

  CallToYieldProc:
    call og_yield_9(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation YieldConsistent_11_9()
{
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    yield;
    assert gConsistent(state);
  **** end structured program */

  og_init:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon01, CallToYieldProc;

  anon05:
    return;

  anon01:
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon05, CallToYieldProc;

  CallToYieldProc:
    call og_yield_9(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation main_9()
{
  var xid: Xid;
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    while (*)
      invariant Inv_8(state, B, votes);
      invariant gConsistent(state);
    {
        call xid := Coordinator_TransactionReq();
    }

    yield;
  **** end structured program */

  og_init:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon3_LoopHead:
    assume linear_pair_available == linear_pair_MapConstBool(false);
    assume state == og_global_old_state;
    assume votes == og_global_old_votes;
    assume B == og_global_old_B;
    assume AllocatedXids == og_global_old_AllocatedXids;
    assume pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assert gConsistent(state);
    goto anon3_LoopDone, anon3_LoopBody;

  anon3_LoopBody:
    goto anon3_LoopBody0, CallToYieldProc;

  anon3_LoopDone:
    goto anon2;

  anon2:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon21, CallToYieldProc;

  anon04:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon3_LoopHead;

  anon00:
    call og_skip_dummy_YieldInv_8_YieldConsistent_9_9_YieldConsistent_10_9_YieldConsistent_11_9();
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon04, CallToYieldProc;

  anon3_LoopBody8:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon3_LoopHead;

  anon3_LoopBody4:
    call og_skip_dummy_YieldInv_8_YieldConsistent_9_9_YieldConsistent_10_9_YieldConsistent_11_9();
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon3_LoopBody8, CallToYieldProc;

  anon3_LoopBody0:
    call xid := Coordinator_TransactionReq_9();
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon3_LoopBody4, CallToYieldProc;

  anon25:
    return;

  anon21:
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon25, CallToYieldProc;

  CallToYieldProc:
    call og_yield_9(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation Coordinator_TransactionReq_9() returns (xid: Xid)
{
  var pair: Pair;
  var pairs: [Pair]bool;
  var snapshot: GState;
  var i: Mid;
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    call xid, pairs := AllocateXid();
    call snapshot := GhostRead();
    i := 1;
    while (i <= numParticipants)
      invariant {:terminates} true;
      invariant Inv_8(state, B, votes);
      invariant pairs == (lambda p: Pair :: pair(xid, mid#Pair(p), p) && i <= mid#Pair(p));
      invariant votes[xid] == -1
         || (forall p: Pair :: pairs[p] ==> UndecidedOrCommitted(state[xid][mid#Pair(p)]));
      invariant Inv_9(state, B, xid);
      invariant gConsistent(state);
      invariant ExistsMonotoneExtension(snapshot, state, xid);
      invariant 1 <= i && i <= numParticipants + 1;
    {
        call pairs, pair := TransferPair(xid, i, pairs);
        async call Participant_VoteReq(xid, i, pair);
        i := i + 1;
    }

  **** end structured program */

  og_init:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon3_LoopHead:
    assume linear_pair_available
       == linear_pair_MapOr(PairSetCollector(pairs), linear_pair_MapConstBool(false));
    assume state == og_global_old_state;
    assume votes == og_global_old_votes;
    assume B == og_global_old_B;
    assume AllocatedXids == og_global_old_AllocatedXids;
    assume pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    assert Inv_9(state, B, xid);
    goto anon3_LoopDone, anon3_LoopBody;

  anon3_LoopBody:
    assume {:partition} i <= numParticipants;
    call pairs, pair := atomic_TransferPair_9(xid, i, pairs);
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(3)))
           == linear_pair_MapConstBool(true));
    goto anon3_LoopBody3, CallToYieldProc;

  anon3_LoopDone:
    assume {:partition} numParticipants < i;
    goto anon2;

  anon2:
    goto anon20, CallToYieldProc;

  anon08:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairSetCollector(pairs), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon3_LoopHead;

  anon00:
    call og_skip_dummy_YieldInv_8_YieldConsistent_9_9_YieldConsistent_10_9();
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    call xid, pairs := atomic_AllocateXid_9();
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    i := 1;
    goto anon08, CallToYieldProc;

  anon3_LoopBody12:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairSetCollector(pairs), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon3_LoopHead;

  anon3_LoopBody8:
    call og_skip_dummy_YieldPairs_8_YieldInv_9_9(xid, pairs, xid);
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairSetCollector(pairs), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon3_LoopBody12, CallToYieldProc;

  anon3_LoopBody3:
    call DummyAsyncTarget_Participant_VoteReq_9(xid, i, pair);
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairSetCollector(pairs), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    i := i + 1;
    goto anon3_LoopBody8, CallToYieldProc;

  anon24:
    return;

  anon20:
    call og_skip_dummy_YieldInv_8_YieldConsistent_9_9_YieldConsistent_10_9();
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairSetCollector(pairs), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon24, CallToYieldProc;

  CallToYieldProc:
    call og_yield_9(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation Participant_VoteReq_9(xid: Xid, mid: Mid, pair: Pair)
{
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    if (*)
    {
        async call Coordinator_VoteYes(xid, mid, pair);
    }
    else
    {
        call SetParticipantAborted(xid, mid, pair);
        async call Coordinator_VoteNo(xid, mid, pair);
    }

    yield;
  **** end structured program */

  og_init:
    og_pc, og_ok, linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := false, false, linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon4_Else:
    // <<< injected gate
    assert pair(xid, mid, pair);
    assert xUndecidedOrAborted(state[xid]);
    // injected gate >>>
    call atomic_SetParticipantAborted_9(xid, mid, pair);
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    // <<< injected gate
    assert AllocatedXids[xid];
    assert pair(xid, mid, pair);
    assert xUndecidedOrAborted(state[xid]);
    // injected gate >>>
    call atomic_Coordinator_VoteNo_9(xid, mid, pair);
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon3;

  anon3:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon31, CallToYieldProc;

  anon4_Then:
    // <<< injected gate
    assert AllocatedXids[xid];
    assert pair(xid, mid, pair);
    assert xConsistent(state[xid]);
    // injected gate >>>
    call atomic_Coordinator_VoteYes_9(xid, mid, pair);
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon3;

  anon00:
    assert og_pc
       || 
      (
        state == og_global_old_state
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (exists #tmp_0_second_newState: XState :: 
        state == og_global_old_state[xid := #tmp_0_second_newState]
           && AllocatedXids == og_global_old_AllocatedXids
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && xConsistentExtension(og_global_old_state[xid], #tmp_0_second_newState));
    assert og_pc
       ==> state == og_global_old_state
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := state == og_global_old_state
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (exists #tmp_0_second_newState: XState :: 
        state == og_global_old_state[xid := #tmp_0_second_newState]
           && AllocatedXids == og_global_old_AllocatedXids
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && xConsistentExtension(og_global_old_state[xid], #tmp_0_second_newState));
    call og_skip_dummy_YieldUndecidedOrCommitted_8_YieldInv_9_9(xid, mid, pair, xid);
    assume og_pc || (AllocatedXids[xid] && pair(xid, mid, pair) && xConsistent(state[xid]));
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapOr(PairCollector(pair), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon4_Then, anon4_Else;

  anon39:
    assert og_pc
       || 
      (
        state == og_global_old_state
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (exists #tmp_0_second_newState: XState :: 
        state == og_global_old_state[xid := #tmp_0_second_newState]
           && AllocatedXids == og_global_old_AllocatedXids
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && xConsistentExtension(og_global_old_state[xid], #tmp_0_second_newState));
    assert og_pc
       ==> state == og_global_old_state
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := state == og_global_old_state
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (exists #tmp_0_second_newState: XState :: 
        state == og_global_old_state[xid := #tmp_0_second_newState]
           && AllocatedXids == og_global_old_AllocatedXids
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && xConsistentExtension(og_global_old_state[xid], #tmp_0_second_newState));
    assert og_ok;
    return;

  anon31:
    assert og_pc
       || 
      (
        state == og_global_old_state
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (exists #tmp_0_second_newState: XState :: 
        state == og_global_old_state[xid := #tmp_0_second_newState]
           && AllocatedXids == og_global_old_AllocatedXids
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && xConsistentExtension(og_global_old_state[xid], #tmp_0_second_newState));
    assert og_pc
       ==> state == og_global_old_state
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := state == og_global_old_state
         && AllocatedXids == og_global_old_AllocatedXids
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (exists #tmp_0_second_newState: XState :: 
        state == og_global_old_state[xid := #tmp_0_second_newState]
           && AllocatedXids == og_global_old_AllocatedXids
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && xConsistentExtension(og_global_old_state[xid], #tmp_0_second_newState));
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume og_pc || (AllocatedXids[xid] && pair(xid, mid, pair) && xConsistent(state[xid]));
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon39, CallToYieldProc;

  CallToYieldProc:
    call og_yield_9(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



procedure {:inline 1} Impl_YieldChecker_YieldInv_9_9(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_YieldConsistent_9_9(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_YieldConsistent_10_9(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_YieldConsistent_11_9(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_main_9(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_Participant_VoteReq_9(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



implementation {:inline 1} Impl_YieldChecker_YieldInv_9_9(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var xid: Xid;
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assume Inv_9(og_global_old_state, og_global_old_B, xid);
    assert Inv_9(state, B, xid);
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_YieldConsistent_9_9(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assume gConsistent(og_global_old_state);
    assert gConsistent(state);
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_YieldConsistent_10_9(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_YieldConsistent_11_9(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_main_9(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var xid: Xid;
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_Participant_VoteReq_9(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var xid: Xid;
  var mid: Mid;
  var pair: Pair;
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assume false;
    return;
}



procedure og_skip_dummy_YieldInv_8_YieldConsistent_9_9_YieldConsistent_10_9_YieldConsistent_11_9();
  requires gConsistent(state);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures gConsistent(state);



procedure og_skip_dummy_YieldInv_8_YieldConsistent_9_9_YieldConsistent_10_9();
  requires gConsistent(state);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures gConsistent(state);



procedure DummyAsyncTarget_Participant_VoteReq_9(xid: Xid, mid: Mid, pair: Pair);
  requires Inv_9(state, B, xid);
  free requires (exists partition_pair: [Pair]int :: 
    linear_pair_MapImp(PairSetCollector(B), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
         == linear_pair_MapConstBool(true)
       && linear_pair_MapImp(PairCollector(pair), 
          linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
         == linear_pair_MapConstBool(true));



procedure og_skip_dummy_YieldPairs_8_YieldInv_9_9(og_0_xid: Xid, og_0_pairs: [Pair]bool, og_1_xid: Xid);
  requires Inv_9(state, B, og_1_xid);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures Inv_9(state, B, og_1_xid);



procedure og_skip_dummy_YieldUndecidedOrCommitted_8_YieldInv_9_9(og_0_xid: Xid, og_0_mid: Mid, og_0_pair: Pair, og_1_xid: Xid);
  requires Inv_9(state, B, og_1_xid);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures Inv_9(state, B, og_1_xid);



procedure {:inline 1} og_yield_9(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



implementation {:inline 1} og_yield_9(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{

  enter:
    goto L_0, L_1, L_2, L_3, L_4, L_5;

  L_0:
    call Impl_YieldChecker_YieldInv_9_9(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;

  L_1:
    call Impl_YieldChecker_YieldConsistent_9_9(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;

  L_2:
    call Impl_YieldChecker_YieldConsistent_10_9(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;

  L_3:
    call Impl_YieldChecker_YieldConsistent_11_9(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;

  L_4:
    call Impl_YieldChecker_main_9(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;

  L_5:
    call Impl_YieldChecker_Participant_VoteReq_9(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;
}



procedure YieldConsistent_10_10();
  requires gConsistent(state);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures gConsistent(state);



procedure YieldConsistent_11_10();
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure main_10();
  requires gUndecided(state);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



procedure Coordinator_TransactionReq_10() returns (xid: Xid);
  requires gConsistent(state);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures gConsistent(state);



implementation YieldConsistent_10_10()
{
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    yield;
    assert gConsistent(state);
  **** end structured program */

  og_init:
    og_pc, og_ok, linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := false, false, linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assert gConsistent(state);
    goto anon02, CallToYieldProc;

  anon011:
    assert og_pc
       || 
      (state == og_global_old_state
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (state == og_global_old_state
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_pc
       ==> state == og_global_old_state
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := state == og_global_old_state
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (state == og_global_old_state
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_ok;
    return;

  anon02:
    assert og_pc
       || 
      (state == og_global_old_state
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (state == og_global_old_state
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    assert og_pc
       ==> state == og_global_old_state
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := state == og_global_old_state
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (state == og_global_old_state
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset);
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume true;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assume gConsistent(state);
    goto anon011, CallToYieldProc;

  CallToYieldProc:
    call og_yield_10(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation YieldConsistent_11_10()
{
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    yield;
    assert gConsistent(state);
  **** end structured program */

  og_init:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon01, CallToYieldProc;

  anon05:
    return;

  anon01:
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon05, CallToYieldProc;

  CallToYieldProc:
    call og_yield_10(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation main_10()
{
  var xid: Xid;
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    while (*)
      invariant Inv_8(state, B, votes);
      invariant gConsistent(state);
    {
        call xid := Coordinator_TransactionReq();
    }

    yield;
  **** end structured program */

  og_init:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon3_LoopHead:
    assume linear_pair_available == linear_pair_MapConstBool(false);
    assume state == og_global_old_state;
    assume votes == og_global_old_votes;
    assume B == og_global_old_B;
    assume AllocatedXids == og_global_old_AllocatedXids;
    assume pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assert gConsistent(state);
    goto anon3_LoopDone, anon3_LoopBody;

  anon3_LoopBody:
    goto anon3_LoopBody0, CallToYieldProc;

  anon3_LoopDone:
    goto anon2;

  anon2:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon21, CallToYieldProc;

  anon04:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon3_LoopHead;

  anon00:
    call og_skip_dummy_YieldInv_8_skip_dummy_YieldConsistent_9_YieldConsistent_10_10_YieldConsistent_11_10();
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon04, CallToYieldProc;

  anon3_LoopBody8:
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon3_LoopHead;

  anon3_LoopBody4:
    call og_skip_dummy_YieldInv_8_skip_dummy_YieldConsistent_9_YieldConsistent_10_10_YieldConsistent_11_10();
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon3_LoopBody8, CallToYieldProc;

  anon3_LoopBody0:
    call xid := Coordinator_TransactionReq_10();
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon3_LoopBody4, CallToYieldProc;

  anon25:
    return;

  anon21:
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon25, CallToYieldProc;

  CallToYieldProc:
    call og_yield_10(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation Coordinator_TransactionReq_10() returns (xid: Xid)
{
  var pair: Pair;
  var pairs: [Pair]bool;
  var snapshot: GState;
  var i: Mid;
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;
  var og_old_xid: Xid;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    call xid, pairs := AllocateXid();
    call snapshot := GhostRead();
    i := 1;
    while (i <= numParticipants)
      invariant {:terminates} true;
      invariant Inv_8(state, B, votes);
      invariant pairs == (lambda p: Pair :: pair(xid, mid#Pair(p), p) && i <= mid#Pair(p));
      invariant votes[xid] == -1
         || (forall p: Pair :: pairs[p] ==> UndecidedOrCommitted(state[xid][mid#Pair(p)]));
      invariant Inv_9(state, B, xid);
      invariant gConsistent(state);
      invariant ExistsMonotoneExtension(snapshot, state, xid);
      invariant 1 <= i && i <= numParticipants + 1;
    {
        call pairs, pair := TransferPair(xid, i, pairs);
        async call Participant_VoteReq(xid, i, pair);
        i := i + 1;
    }

  **** end structured program */

  og_init:
    og_pc, og_ok, linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset, og_old_xid := false, false, linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset, xid;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon3_LoopHead:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    assert gConsistent(state);
    assert ExistsMonotoneExtension(snapshot, state, xid);
    assert 1 <= i && i <= numParticipants + 1;
    goto anon3_LoopDone, anon3_LoopBody;

  anon3_LoopBody:
    assume {:partition} i <= numParticipants;
    call pairs, pair := atomic_TransferPair_10(xid, i, pairs);
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairCollector(pair), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(3)))
           == linear_pair_MapConstBool(true));
    // <<< injected gate
    assert AllocatedXids[xid];
    assert pair(xid, i, pair);
    assert xConsistent(state[xid]);
    // injected gate >>>
    call atomic_Participant_VoteReq_10(xid, i, pair);
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    i := i + 1;
    call skip_dummy_YieldPairs_8(xid, pairs);
    call skip_dummy_YieldInv_9(xid);
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon3_LoopHead;

  anon3_LoopDone:
    assume {:partition} numParticipants < i;
    goto anon2;

  anon2:
    goto anon20, CallToYieldProc;

  anon00:
    assert og_pc
       || 
      (state == og_global_old_state
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (exists #tmp_0_second_newState: XState :: 
        state == og_global_old_state[xid := #tmp_0_second_newState]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && xid == xid
           && xConsistent(#tmp_0_second_newState));
    assert og_pc
       ==> state == og_global_old_state
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && xid == og_old_xid;
    og_pc, og_ok := state == og_global_old_state
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (exists #tmp_0_second_newState: XState :: 
        state == og_global_old_state[xid := #tmp_0_second_newState]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && xid == xid
           && xConsistent(#tmp_0_second_newState));
    call og_skip_dummy_YieldInv_8_skip_dummy_YieldConsistent_9_YieldConsistent_10_10();
    assume og_pc || true;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset, og_old_xid := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset, xid;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    call xid, pairs := atomic_AllocateXid_10();
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    call snapshot := GhostRead();
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    i := 1;
    goto anon3_LoopHead;

  anon28:
    assert og_pc
       || 
      (state == og_global_old_state
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (exists #tmp_0_second_newState: XState :: 
        state == og_global_old_state[xid := #tmp_0_second_newState]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && xid == xid
           && xConsistent(#tmp_0_second_newState));
    assert og_pc
       ==> state == og_global_old_state
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && xid == og_old_xid;
    og_pc, og_ok := state == og_global_old_state
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (exists #tmp_0_second_newState: XState :: 
        state == og_global_old_state[xid := #tmp_0_second_newState]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && xid == xid
           && xConsistent(#tmp_0_second_newState));
    assert og_ok;
    return;

  anon20:
    assert og_pc
       || 
      (state == og_global_old_state
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset)
       || (exists #tmp_0_second_newState: XState :: 
        state == og_global_old_state[xid := #tmp_0_second_newState]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && xid == xid
           && xConsistent(#tmp_0_second_newState));
    assert og_pc
       ==> state == og_global_old_state
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
         && xid == og_old_xid;
    og_pc, og_ok := state == og_global_old_state
         && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       ==> og_pc, og_ok
       || (exists #tmp_0_second_newState: XState :: 
        state == og_global_old_state[xid := #tmp_0_second_newState]
           && pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
           && xid == xid
           && xConsistent(#tmp_0_second_newState));
    call og_skip_dummy_YieldInv_8_skip_dummy_YieldConsistent_9_YieldConsistent_10_10();
    assume og_pc || true;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset, og_old_xid := linear_pair_MapOr(PairSetCollector(pairs), linear_pair_MapConstBool(false)), state, votes, B, AllocatedXids, pendingAsyncMultiset, xid;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(pairs), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(2)))
           == linear_pair_MapConstBool(true));
    goto anon28, CallToYieldProc;

  CallToYieldProc:
    call og_yield_10(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



procedure {:inline 1} Impl_YieldChecker_YieldConsistent_10_10(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_YieldConsistent_11_10(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_main_10(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



implementation {:inline 1} Impl_YieldChecker_YieldConsistent_10_10(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assume gConsistent(og_global_old_state);
    assert gConsistent(state);
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_YieldConsistent_11_10(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_main_10(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var xid: Xid;
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assume false;
    return;
}



procedure og_skip_dummy_YieldInv_8_skip_dummy_YieldConsistent_9_YieldConsistent_10_10_YieldConsistent_11_10();
  requires gConsistent(state);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures gConsistent(state);



procedure og_skip_dummy_YieldInv_8_skip_dummy_YieldConsistent_9_YieldConsistent_10_10();
  requires gConsistent(state);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures gConsistent(state);



procedure {:inline 1} og_yield_10(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



implementation {:inline 1} og_yield_10(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{

  enter:
    goto L_0, L_1, L_2;

  L_0:
    call Impl_YieldChecker_YieldConsistent_10_10(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;

  L_1:
    call Impl_YieldChecker_YieldConsistent_11_10(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;

  L_2:
    call Impl_YieldChecker_main_10(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;
}



procedure YieldConsistent_11_11();
  requires gConsistent(state);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures gConsistent(state);



procedure main_11();
  requires gUndecided(state);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;



implementation YieldConsistent_11_11()
{
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;
  var linear_pair_available: [Pair]bool;

  /*** structured program:
    yield;
    assert gConsistent(state);
  **** end structured program */

  og_init:
    og_pc, og_ok, linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := false, false, linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assert gConsistent(state);
    goto anon02, CallToYieldProc;

  anon011:
    assert og_pc
       || 
      pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assert og_pc ==> pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := pendingAsyncMultiset == og_global_old_pendingAsyncMultiset ==> og_pc, og_ok || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assert og_ok;
    return;

  anon02:
    assert og_pc
       || 
      pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assert og_pc ==> pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := pendingAsyncMultiset == og_global_old_pendingAsyncMultiset ==> og_pc, og_ok || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume true;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assume gConsistent(state);
    goto anon011, CallToYieldProc;

  CallToYieldProc:
    call og_yield_11(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



implementation main_11()
{
  var xid: Xid;
  var og_global_old_state: GState;
  var og_global_old_votes: [Xid]int;
  var og_global_old_B: [Pair]bool;
  var og_global_old_AllocatedXids: [Xid]bool;
  var og_global_old_pendingAsyncMultiset: [PendingAsync]int;
  var og_pc: bool;
  var og_ok: bool;
  var linear_pair_available: [Pair]bool;
  var og_pc_anon3_LoopHead: bool;
  var og_ok_anon3_LoopHead: bool;

  /*** structured program:
    while (*)
      invariant Inv_8(state, B, votes);
      invariant gConsistent(state);
    {
        call xid := Coordinator_TransactionReq();
    }

    yield;
  **** end structured program */

  og_init:
    og_pc, og_pc_anon3_LoopHead, og_ok, og_ok_anon3_LoopHead, linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := false, false, false, false, linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon0;

  anon0:
    goto anon00, CallToYieldProc;

  anon3_LoopHead:
    assert og_pc_anon3_LoopHead == og_pc;
    assert og_ok_anon3_LoopHead ==> og_ok;
    assume linear_pair_available == linear_pair_MapConstBool(false);
    assume state == og_global_old_state;
    assume votes == og_global_old_votes;
    assume B == og_global_old_B;
    assume AllocatedXids == og_global_old_AllocatedXids;
    assume pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assert gConsistent(state);
    goto anon3_LoopDone, anon3_LoopBody;

  anon3_LoopBody:
    call xid := atomic_Coordinator_TransactionReq_11();
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon3_LoopBody2, CallToYieldProc;

  anon3_LoopDone:
    goto anon2;

  anon2:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon21, CallToYieldProc;

  anon08:
    assert og_pc
       || 
      pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assert og_pc ==> pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := pendingAsyncMultiset == og_global_old_pendingAsyncMultiset ==> og_pc, og_ok || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc_anon3_LoopHead, og_ok_anon3_LoopHead := og_pc, og_ok;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon3_LoopHead;

  anon00:
    assert og_pc
       || 
      pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assert og_pc ==> pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := pendingAsyncMultiset == og_global_old_pendingAsyncMultiset ==> og_pc, og_ok || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    call og_skip_dummy_YieldInv_8_skip_dummy_YieldConsistent_9_skip_dummy_YieldConsistent_10_YieldConsistent_11_11();
    assume true;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon08, CallToYieldProc;

  anon3_LoopBody10:
    assert og_pc
       || 
      pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assert og_pc ==> pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := pendingAsyncMultiset == og_global_old_pendingAsyncMultiset ==> og_pc, og_ok || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    goto anon3_LoopHead;

  anon3_LoopBody2:
    assert og_pc
       || 
      pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assert og_pc ==> pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := pendingAsyncMultiset == og_global_old_pendingAsyncMultiset ==> og_pc, og_ok || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    call og_skip_dummy_YieldInv_8_skip_dummy_YieldConsistent_9_skip_dummy_YieldConsistent_10_YieldConsistent_11_11();
    assume true;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon3_LoopBody10, CallToYieldProc;

  anon29:
    assert og_pc
       || 
      pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assert og_pc ==> pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := pendingAsyncMultiset == og_global_old_pendingAsyncMultiset ==> og_pc, og_ok || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assert og_ok;
    return;

  anon21:
    assert og_pc
       || 
      pendingAsyncMultiset == og_global_old_pendingAsyncMultiset
       || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    assert og_pc ==> pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    og_pc, og_ok := pendingAsyncMultiset == og_global_old_pendingAsyncMultiset ==> og_pc, og_ok || pendingAsyncMultiset == og_global_old_pendingAsyncMultiset;
    havoc state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume true;
    linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset := linear_pair_MapConstBool(false), state, votes, B, AllocatedXids, pendingAsyncMultiset;
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_hole, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    goto anon29, CallToYieldProc;

  CallToYieldProc:
    call og_yield_11(linear_pair_available, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    assume false;
    return;
}



procedure {:inline 1} Impl_YieldChecker_YieldConsistent_11_11(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



procedure {:inline 1} Impl_YieldChecker_main_11(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



implementation {:inline 1} Impl_YieldChecker_YieldConsistent_11_11(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assume gConsistent(og_global_old_state);
    assert gConsistent(state);
    assume false;
    return;
}



implementation {:inline 1} Impl_YieldChecker_main_11(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{
  var xid: Xid;
  var og_local_old_state: GState;
  var og_local_old_votes: [Xid]int;
  var og_local_old_B: [Pair]bool;
  var og_local_old_AllocatedXids: [Xid]bool;
  var og_local_old_pendingAsyncMultiset: [PendingAsync]int;

  enter:
    goto exit, L0;

  exit:
    return;

  L0:
    assume (exists partition_pair: [Pair]int :: 
      linear_pair_MapImp(linear_pair_in, linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(0)))
           == linear_pair_MapConstBool(true)
         && linear_pair_MapImp(PairSetCollector(og_global_old_B), 
            linear_pair_MapEq(partition_pair, linear_pair_MapConstInt(1)))
           == linear_pair_MapConstBool(true));
    assume false;
    return;
}



procedure og_skip_dummy_YieldInv_8_skip_dummy_YieldConsistent_9_skip_dummy_YieldConsistent_10_YieldConsistent_11_11();
  requires gConsistent(state);
  modifies state, votes, B, AllocatedXids, pendingAsyncMultiset;
  ensures gConsistent(state);



procedure {:inline 1} og_yield_11(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int);



implementation {:inline 1} og_yield_11(linear_pair_in: [Pair]bool, 
    og_global_old_state: GState, 
    og_global_old_votes: [Xid]int, 
    og_global_old_B: [Pair]bool, 
    og_global_old_AllocatedXids: [Xid]bool, 
    og_global_old_pendingAsyncMultiset: [PendingAsync]int)
{

  enter:
    goto L_0, L_1;

  L_0:
    call Impl_YieldChecker_YieldConsistent_11_11(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;

  L_1:
    call Impl_YieldChecker_main_11(linear_pair_in, og_global_old_state, og_global_old_votes, og_global_old_B, og_global_old_AllocatedXids, og_global_old_pendingAsyncMultiset);
    return;
}


