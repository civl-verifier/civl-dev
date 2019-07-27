// The VoteNo atomic action
procedure {:inline 1} VoteNo (xid: Xid)
modifies state;
{
  var oldState, newState: XState;
  oldState := state[xid];
  assume xUndecidedOrAborted(newState);
  assume xConsistentExtension(oldState, newState);
  state[xid] := newState;
}

// procedure {:inline 1} VoteNo' (xid: Xid)
// modifies state;
// {
//   var {:prophecy} newState: XState;
//   state[xid] := newState;
//   assume xUndecidedOrAborted(newState);
//   assume xConsistentExtension(state[xid], newState);
//   newState =: state[xid];
// }

// Transition relation of VoteNo
function tr_VoteNo(xid:Xid, state:GState, state':GState) : bool
{
  (forall xx:Xid :: xx != xid ==> state'[xx] == state[xx]) &&
  xUndecidedOrAborted(state'[xid]) &&
  xConsistentExtension(state[xid], state'[xid])
}

function witness(state:GState, state':GState, first_xid:Xid, second_xid:Xid) : GState
{
   state[second_xid := state'[second_xid]]
}

procedure CommutativityChecker_VoteNo_VoteNo(first_xid: Xid, second_xid: Xid)
  requires xUndecidedOrAborted(state[first_xid]);
  requires xUndecidedOrAborted(state[second_xid]);
  modifies state;
{
  call VoteNo(first_xid);
  call VoteNo(second_xid);

  // Plain commutativity check, patching transition relations with existential quantifier
  assert (exists state':GState :: tr_VoteNo(second_xid, old(state), state') && tr_VoteNo(first_xid, state', state));

  // User-supplied witness
  assert tr_VoteNo(second_xid, old(state), witness(old(state), state, first_xid, second_xid)) &&
         tr_VoteNo(first_xid, witness(old(state), state, first_xid, second_xid), state);
  
  // Check computed without witness inference
  assert
    (exists #tmp_0_second_newState: XState, #tmp_1_first_newState: XState :: 
           state
           == old(state)[second_xid := #tmp_0_second_newState][first_xid := #tmp_1_first_newState]
         && xConsistentExtension(old(state)[second_xid := #tmp_0_second_newState][first_xid], 
          #tmp_1_first_newState)
         && xUndecidedOrAborted(#tmp_1_first_newState)
         && xConsistentExtension(old(state)[second_xid], #tmp_0_second_newState)
         && xUndecidedOrAborted(#tmp_0_second_newState));

  // Check computed with witness inference
  assert (exists #tmp_0_second_newState: XState :: 
           state
           == old(state)[second_xid := #tmp_0_second_newState][first_xid := state[first_xid]]
         && xConsistentExtension(old(state)[second_xid := #tmp_0_second_newState][first_xid], state[first_xid])
         && xUndecidedOrAborted(state[first_xid])
         && xConsistentExtension(old(state)[second_xid], #tmp_0_second_newState)
         && xUndecidedOrAborted(#tmp_0_second_newState));
}

// ###########################################################################
// Type declarations

type Xid = int;
type Mid = int;

const CoordinatorMid : Mid;
axiom CoordinatorMid == 0;
function coordinatorMid (mid : Mid) : bool { mid == CoordinatorMid }

const numParticipants : int;
axiom 0 < numParticipants;
function participantMid (mid : Mid) : bool { 1 <= mid && mid <= numParticipants }

type {:datatype} Pair;
function {:constructor} Pair (xid: Xid, mid: Mid) : Pair;

function {:inline} pair (xid: Xid, mid: Mid, p: Pair) : bool
{ p == Pair(xid, mid) && participantMid(mid#Pair(p)) }

// Transaction State
type MState = int;
function {:inline} ABORTED   () : int { 0 }
function {:inline} UNDECIDED () : int { 1 }
function {:inline} COMMITTED () : int { 2 }
function {:inline} Aborted   (i:MState) : bool { i == ABORTED() }
function {:inline} Undecided (i:MState) : bool { i == UNDECIDED() }
function {:inline} Committed (i:MState) : bool { i == COMMITTED() }
function {:inline} UndecidedOrAborted   (i:MState) : bool { Undecided(i) || Aborted(i) }
function {:inline} UndecidedOrCommitted (i:MState) : bool { Undecided(i) || Committed(i) }

type XState = [Mid]MState;
type GState = [Xid]XState;

// ###########################################################################
// Global shared variables

var state: GState;

// ###########################################################################
// Consistency Predicates

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
