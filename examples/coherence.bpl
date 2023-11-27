type MemAddr;

type Value;

datatype State {
  Modified(),
  Exclusive(),
  Shared(),
  Invalid()
}

type CacheAddr;

datatype CacheRequest {
  ReadShared(ma: MemAddr),
  ReadOwn(ma: MemAddr),
  Write(ma: MemAddr, value: Value),
  NoCacheRequest()
}

datatype CacheLine {
  CacheLine(ma: MemAddr, value: Value, state: State, currRequest: CacheRequest)
}

type Cache = [CacheAddr]CacheLine;

type CacheId;
const i0: CacheId;

function Hash(MemAddr): CacheAddr;

datatype DirState {
  Owner(i: CacheId),
  Sharers(iset: Set CacheId)
}

datatype DirRequest {
  Share(i: CacheId),
  Own(i: CacheId),
  Evict(i: CacheId),
  NoDirRequest()
}

datatype DirInfo {
  DirInfo(state: DirState, currRequest: DirRequest)
}

datatype DirRequestPermission {
  DirRequestPermission(i: CacheId, ca: CacheAddr)
}

datatype DirPermission {
  DirPermission(i: CacheId, ma: MemAddr)
}

function {:inline} WholeDirPermission(ma: MemAddr): Lset DirPermission {
  Lset((lambda {:pool "DirPermission"} x: DirPermission :: x->ma == ma))
}

datatype SnoopPermission {
  SnoopPermission(i: CacheId, ma: MemAddr, ticket: int)
}

var {:layer 0,3} mem: [MemAddr]Value;
var {:layer 0,3} dir: [MemAddr]DirInfo;
var {:layer 0,3} cache: [CacheId]Cache;

var {:layer 0,3} front: [CacheId][MemAddr]int;
var {:layer 0,3} back: [CacheId][MemAddr]int;

var {:layer 1,3} dirRequestPermissionsAtCache: Lset DirRequestPermission;
var {:layer 1,3} dirRequestPermissionsAtDir: Lset DirRequestPermission;
var {:layer 1,3} snoopPermissions: Lset SnoopPermission;
var {:layer 1,3} dirPermissions: Lset DirPermission;


// at cache
yield procedure {:layer 2} cache_read_share_req(i: CacheId, ma: MemAddr) returns (result: Option Value)
{
  var line: CacheLine;
  var {:layer 1,2} drp: Lset DirRequestPermission;
  call result, line, drp := cache_req_begin(i, ReadShared(ma));
  if (result is Some) {
    return;
  }
  if (line->currRequest is NoCacheRequest) {
    // cache[i][Hash(ma)]->currRequest was set to this request
    if (line->state == Invalid()) {
      async call dir_read_share_req(i, ma, drp);
    } else if (line->state == Modified()) {
      async call dir_evict_req(i, line->ma, Some(line->value), drp);
    } else {
      async call dir_evict_req(i, line->ma, None(), drp);
    }
  }
}

yield procedure {:layer 2} cache_read_own_req(i: CacheId, ma: MemAddr) returns (result: Option Value)
{
  var line: CacheLine;
  var {:layer 1,2} drp: Lset DirRequestPermission;
  call result, line, drp := cache_req_begin(i, ReadOwn(ma));
  if (result is Some) {
    return;
  }
  if (line->currRequest is NoCacheRequest) {
    // cache[i][Hash(ma)]->currRequest was set to this request
    if (line->state == Invalid() || line->ma == ma) {
      async call dir_read_own_req(i, ma, drp);
    } else if (line->state == Modified()) {
      async call dir_evict_req(i, line->ma, Some(line->value), drp);
    } else {
      async call dir_evict_req(i, line->ma, None(), drp);
    }
  }
}

yield procedure {:layer 2} cache_write_req(i: CacheId, ma: MemAddr, v: Value) returns (result: Option Value)
{
  var line: CacheLine;
  var {:layer 1,2} drp: Lset DirRequestPermission;
  result := None();
  call result, line, drp := cache_req_begin(i, Write(ma, v));
  if (result is Some) {
    return;
  }
  if (line->currRequest is NoCacheRequest) {
    // cache[i][Hash(ma)]->currRequest was set to this request
    if (line->state == Invalid() || line->ma == ma) {
      async call dir_read_own_req(i, ma, drp);
    } else if (line->state == Modified()) {
      async call dir_evict_req(i, line->ma, Some(line->value), drp);
    } else {
      async call dir_evict_req(i, line->ma, None(), drp);
    }
  }
}

atomic action {:layer 2} atomic_cache_req_begin(i: CacheId, currRequest: CacheRequest) returns (result: Option Value, line: CacheLine, drp: Lset DirRequestPermission)
modifies cache, dirRequestPermissionsAtCache;
{
  call result, line := primitive_cache_req_begin(i, currRequest);
  if (result is None && line->currRequest is NoCacheRequest) {
    drp := Lset(MapOne(DirRequestPermission(i, Hash(currRequest->ma))));
    call Lset_Split(dirRequestPermissionsAtCache, drp);
  } else {
    call drp := Lset_Empty();
  }
}
yield procedure {:layer 1} cache_req_begin(i: CacheId, currRequest: CacheRequest) returns (result: Option Value, line: CacheLine, {:layer 1} drp: Lset DirRequestPermission)
refines atomic_cache_req_begin;
{
  call result, line := cache_req_begin#0(i, currRequest);
  if (result is None && line->currRequest is NoCacheRequest) {
    drp := Lset(MapOne(DirRequestPermission(i, Hash(currRequest->ma))));
    call {:layer 1} Lset_Split(dirRequestPermissionsAtCache, drp);
  } else {
    call {:layer 1} drp := Lset_Empty();
  }
}

atomic action {:layer 1} atomic_cache_req_begin#0(i: CacheId, currRequest: CacheRequest) returns (result: Option Value, line: CacheLine)
modifies cache;
{
  call result, line := primitive_cache_req_begin(i, currRequest);
}
yield procedure {:layer 0} cache_req_begin#0(i: CacheId, currRequest: CacheRequest) returns (result: Option Value, line: CacheLine);
refines atomic_cache_req_begin#0;

action {:layer 1,2} primitive_cache_req_begin(i: CacheId, currRequest: CacheRequest) returns (result: Option Value, line: CacheLine)
modifies cache;
{
  var ca: CacheAddr;
  var ma: MemAddr;
  assert !(currRequest is NoCacheRequest);
  ma := currRequest->ma;
  ca := Hash(ma);
  line := cache[i][ca];
  result := None();
  assert line->state == Invalid() || Hash(line->ma) == ca;
  if (currRequest is ReadShared && line->state != Invalid() && line->ma == ma) {
    result := Some(line->value);
    return;
  }
  if (currRequest is ReadOwn && (line->state == Exclusive() || line->state == Modified()) && line->ma == ma) {
    result := Some(line->value);
    return;
  }
  if (currRequest is Write && (line->state == Exclusive() || line->state == Modified()) && line->ma == ma) {
    cache[i][ca]->state := Modified();
    cache[i][ca]->value := currRequest->value;
    result := Some(currRequest->value);
    return;
  }
  if (cache[i][ca]->currRequest is NoCacheRequest) {
    cache[i][ca]->currRequest := currRequest;
  }
}

async atomic action {:layer 3} atomic_cache_read_resp(i: CacheId, ma: MemAddr, v: Value, s: State, ticket: int, {:linear_in} drp: Lset DirRequestPermission, {:linear_in} sp: Lval SnoopPermission)
modifies cache, front, dirRequestPermissionsAtCache;
{
  assert Lset_Contains(drp, DirRequestPermission(i, Hash(ma)));
  assert sp == Lval(SnoopPermission(i, ma, ticket));
  call primitive_cache_read_resp_begin(i, ma, v, s);
  call Lset_Transfer(dirRequestPermissionsAtCache, drp);
}
yield procedure {:layer 2} cache_read_resp(i: CacheId, ma: MemAddr, v: Value, s: State, ticket: int, {:layer 1,2} {:linear_in} drp: Lset DirRequestPermission, {:layer 1,2} {:linear_in} sp: Lval SnoopPermission)
refines atomic_cache_read_resp;
{
  call wait_front(i, ma, ticket);
  call cache_read_resp_begin(i, ma, v, s, drp);
  call increment_front(i, ma);
}

atomic action {:layer 2} atomic_cache_read_resp_begin(i: CacheId, ma: MemAddr, v: Value, s: State, {:linear_in} drp: Lset DirRequestPermission)
modifies cache, front, dirRequestPermissionsAtCache;
{
  call primitive_cache_read_resp_begin(i, ma, v, s);
  call Lset_Transfer(dirRequestPermissionsAtCache, drp);
}
yield procedure {:layer 1} cache_read_resp_begin(i: CacheId, ma: MemAddr, v: Value, s: State, {:layer 1} {:linear_in} drp: Lset DirRequestPermission)
refines atomic_cache_read_resp_begin;
{
  call cache_read_resp_begin#0(i, ma, v, s);
  call {:layer 1} Lset_Transfer(dirRequestPermissionsAtCache, drp);
}

atomic action {:layer 1} atomic_cache_read_resp_begin#0(i: CacheId, ma: MemAddr, v: Value, s: State)
modifies cache;
{
  call primitive_cache_read_resp_begin(i, ma, v, s);
}
yield procedure {:layer 0} cache_read_resp_begin#0(i: CacheId, ma: MemAddr, v: Value, s: State);
refines atomic_cache_read_resp_begin#0;

action {:layer 1,3} primitive_cache_read_resp_begin(i: CacheId, ma: MemAddr, v: Value, s: State)
modifies cache;
{
  var currRequest: CacheRequest;
  var ca: CacheAddr;
  ca := Hash(ma);
  currRequest := cache[i][ca]->currRequest;
  assert currRequest->ma == ma;
  if (currRequest is ReadShared) {
    assert s == Shared();
  } else if (currRequest is ReadOwn || currRequest is Write) {
    assert s == Exclusive();
  } else {
    assert false;
  }
  cache[i][ca] := CacheLine(ma, v, s, NoCacheRequest());
}

yield procedure {:layer 2} cache_evict_resp(i: CacheId, ma: MemAddr, ticket: int, {:layer 1,2} {:linear_in} drp: Lset DirRequestPermission, {:layer 1,2} {:linear_in} sp: Lval SnoopPermission)
{
  var currRequest: CacheRequest;
  call wait_front(i, ma, ticket);
  call currRequest := cache_evict_resp_begin(i, ma);
  call increment_front(i, ma);
  if (currRequest is ReadShared) {
    async call dir_read_share_req(i, currRequest->ma, drp);
  } else {
    async call dir_read_own_req(i, currRequest->ma, drp);
  }
}

atomic action {:layer 1,2} atomic_cache_evict_resp_begin(i: CacheId, ma: MemAddr) returns (currRequest: CacheRequest)
modifies cache;
{
  call currRequest := primitive_cache_evict_resp_begin(i, ma);
}
yield procedure {:layer 0} cache_evict_resp_begin(i: CacheId, ma: MemAddr) returns (currRequest: CacheRequest);
refines atomic_cache_evict_resp_begin;

action {:layer 1,2} primitive_cache_evict_resp_begin(i: CacheId, ma: MemAddr) returns (currRequest: CacheRequest)
modifies cache;
{
  var line: CacheLine;
  var ca: CacheAddr;
  ca := Hash(ma);
  line := cache[i][ca];
  assert line->ma == ma;
  assert !(line->currRequest is NoCacheRequest);
  cache[i][ca]->state := Invalid();
}

async atomic action {:layer 3} atomic_cache_snoop_exclusive_req(i: CacheId, ma: MemAddr, s: State, ticket: int, {:linear_in} dp: Lset DirPermission, {:linear_in} sp: Lval SnoopPermission)
modifies cache;
creates atomic_dir_snoop_exclusive_resp;
{
  var opt_value: Option Value;
  var asyncCall: atomic_dir_snoop_exclusive_resp;
  call opt_value := primitive_cache_snoop_exclusive_req_begin(i, ma, s);
  asyncCall := atomic_dir_snoop_exclusive_resp(i, ma, opt_value, dp, sp);
  call create_async(asyncCall);
}
yield procedure {:layer 2} cache_snoop_exclusive_req(i: CacheId, ma: MemAddr, s: State, ticket: int, {:layer 1,2} {:linear_in} dp: Lset DirPermission, {:layer 1,2} {:linear_in} sp: Lval SnoopPermission)
refines atomic_cache_snoop_exclusive_req;
{
  var opt_value: Option Value;
  call wait_front(i, ma, ticket);
  call opt_value := cache_snoop_exclusive_req_begin(i, ma, s);
  async call dir_snoop_exclusive_resp(i, ma, opt_value, dp, sp);
}

atomic action {:layer 1,2} atomic_cache_snoop_exclusive_req_begin(i: CacheId, ma: MemAddr, s: State) returns (opt_value: Option Value)
modifies cache;
{
  call opt_value := primitive_cache_snoop_exclusive_req_begin(i, ma, s);
}
yield procedure {:layer 0} cache_snoop_exclusive_req_begin(i: CacheId, ma: MemAddr, s: State) returns (opt_value: Option Value);
refines atomic_cache_snoop_exclusive_req_begin;

action {:layer 1,3} primitive_cache_snoop_exclusive_req_begin(i: CacheId, ma: MemAddr, s: State) returns (opt_value: Option Value)
modifies cache;
{
  var ca: CacheAddr;
  var line: CacheLine;
  ca := Hash(ma);
  line := cache[i][ca];
  assert s == Invalid() || s == Shared();
  assert line->ma == ma;
  if (line->state == Modified()) {
    opt_value := Some(line->value);
  } else if (line->state == Exclusive()) {
    opt_value := None();
  } else {
    assert false;
  }
  cache[i][ca]->state := s;
}

async atomic action {:layer 3} atomic_cache_snoop_shared_req(i: CacheId, ma: MemAddr, ticket: int, {:linear_in} dpOne: Lset DirPermission, {:linear_in} sp: Lval SnoopPermission)
modifies cache;
creates atomic_dir_snoop_shared_resp;
{
  var asyncCall: atomic_dir_snoop_shared_resp;
  call primitive_cache_snoop_shared_req_begin(i, ma);
  asyncCall := atomic_dir_snoop_shared_resp(i, ma, dpOne, sp);
  call create_async(asyncCall);
}
yield procedure {:layer 2} cache_snoop_shared_req(i: CacheId, ma: MemAddr, ticket: int, {:layer 1,2} {:linear_in} dpOne: Lset DirPermission, {:layer 1,2} {:linear_in} sp: Lval SnoopPermission)
refines atomic_cache_snoop_shared_req;
{
  call wait_front(i, ma, ticket);
  call cache_snoop_shared_req_begin(i, ma);
  async call dir_snoop_shared_resp(i, ma, dpOne, sp);
}

atomic action {:layer 1,2} atomic_cache_snoop_shared_req_begin(i: CacheId, ma: MemAddr)
modifies cache;
{
  call primitive_cache_snoop_shared_req_begin(i, ma);
}
yield procedure {:layer 0} cache_snoop_shared_req_begin(i: CacheId, ma: MemAddr);
refines atomic_cache_snoop_shared_req_begin;

action {:layer 1,3} primitive_cache_snoop_shared_req_begin(i: CacheId, ma: MemAddr)
modifies cache;
{
  var ca: CacheAddr;
  var line: CacheLine;
  ca := Hash(ma);
  line := cache[i][ca];
  assert line->ma == ma;
  assert line->state == Shared();
  cache[i][ca]->state := Invalid();
}


// at dir
yield procedure {:layer 2} dir_read_share_req(i: CacheId, ma: MemAddr, {:layer 1,2} {:linear_in} drp: Lset DirRequestPermission)
{
  var dirInfo: DirInfo;
  var dirState: DirState;
  var ticket: int;
  var value: Value;
  var {:layer 1,2} drp': Lset DirRequestPermission;
  var {:layer 1,2} dp: Lset DirPermission;
  var {:layer 1,2} sp: Lval SnoopPermission;
  call dirInfo, drp', dp := dir_req_begin(ma, Share(i), drp);
  dirState := dirInfo->state;
  if (dirState is Owner) {
    call ticket, sp := read_back(dirState->i, ma, dp);
    async call cache_snoop_exclusive_req(dirState->i, ma, Shared(), ticket, dp, sp);
  } else {
    call value := read_mem(ma, dp);
    call ticket, sp := increment_back(i, ma, dp);
    call dir_req_end(ma, if dirState->iset == Set_Empty() then Owner(i) else Sharers(Set_Add(dirState->iset, i)), dp);
    async call cache_read_resp(i, ma, value, if dirState->iset == Set_Empty() then Exclusive() else Shared(), ticket, drp', sp);
  }
}

yield procedure {:layer 2} dir_read_own_req(i: CacheId, ma: MemAddr, {:layer 1,2} {:linear_in} drp: Lset DirRequestPermission)
{
  var dirInfo: DirInfo;
  var dirState: DirState;
  var ticket: int;
  var value: Value;
  var {:layer 1,2} drp': Lset DirRequestPermission;
  var {:layer 1,2} dp: Lset DirPermission;
  var {:layer 1,2} sp: Lval SnoopPermission;
  var {:layer 1,2} dpOne: Lset DirPermission;

  var victims: Set CacheId;
  var victim: CacheId;

  call dirInfo, drp', dp := dir_req_begin(ma, Own(i), drp);
  dirState := dirInfo->state;
  if (dirState is Owner) {
    call ticket, sp := read_back(dirState->i, ma, dp);
    async call cache_snoop_exclusive_req(dirState->i, ma, Invalid(), ticket, dp, sp);
  } else if (dirState == Sharers(Set_Empty())) {
    call value := read_mem(ma, dp);
    call ticket, sp := increment_back(i, ma, dp);
    call dir_req_end(ma, if dirState->iset == Set_Empty() then Owner(i) else Sharers(Set_Add(dirState->iset, i)), dp);
    async call cache_read_resp(i, ma, value, if dirState->iset == Set_Empty() then Exclusive() else Shared(), ticket, drp', sp);
  } else {
    victims := dirState->iset;
    while (victims != Set_Empty())
    invariant {:yields} {:layer 1} true;
    {
      victim := Set_Choose(victims);
      victims := Set_Remove(victims, victim);
      dpOne := Lset(MapOne(DirPermission(victim, ma)));
      call {:layer 1,2} Lset_Split(dp, dpOne);
      call ticket, sp := read_back(victim, ma, dpOne);
      async call cache_snoop_shared_req(victim, ma, ticket, dpOne, sp);
    }
  }
}

yield procedure {:layer 2} dir_evict_req(i: CacheId, ma: MemAddr, opt_value: Option Value, {:layer 1,2} {:linear_in} drp: Lset DirRequestPermission)
{
  var dirInfo: DirInfo;
  var dirState: DirState;
  var ticket: int;
  var {:layer 1,2} drp': Lset DirRequestPermission;
  var {:layer 1,2} dp: Lset DirPermission;
  var {:layer 1,2} sp: Lval SnoopPermission;
  call dirInfo, drp', dp := dir_req_begin(ma, Evict(i), drp);
  if (opt_value is Some) {
    call write_mem(ma, opt_value->t, dp);
  }
  dirState := dirInfo->state;
  call ticket, sp := increment_back(i, ma, dp);
  call dir_req_end(ma, if dirState is Owner then Sharers(Set_Empty()) else Sharers(Set_Remove(dirState->iset, i)), dp);
  async call cache_evict_resp(i, ma, ticket, drp', sp);
}

async atomic action {:layer 3} atomic_dir_snoop_exclusive_resp(i: CacheId, ma: MemAddr, opt_value: Option Value, {:linear_in} dp: Lset DirPermission, {:linear_in} sp: Lval SnoopPermission)
modifies mem, dir, back, dirPermissions, snoopPermissions, dirRequestPermissionsAtDir;
creates atomic_cache_read_resp;
{
  var dirInfo: DirInfo;
  var dirState: DirState;
  var currRequest: DirRequest;
  var ticket: int;
  var value: Value;
  var drp': Lset DirRequestPermission;
  var sp': Lval SnoopPermission;
  var asyncCall: atomic_cache_read_resp;
  if (opt_value is Some) {
    mem[ma] := opt_value->t;
  }
  dirInfo := dir[ma];
  dirState := dirInfo->state;
  assert dirState is Owner;
  assert dirState->i == i;
  currRequest := dirInfo->currRequest;
  assert !(currRequest is NoDirRequest);
  call Lset_Transfer(dirPermissions, dp);
  call Lval_Transfer(snoopPermissions, sp);
  value := mem[ma];
  ticket := back[currRequest->i][ma];
  back[currRequest->i][ma] := ticket + 1;
  drp' := Lset(MapOne(DirRequestPermission(currRequest->i, Hash(ma))));
  call Lset_Split(dirRequestPermissionsAtDir, drp');
  sp' := Lval(SnoopPermission(currRequest->i, ma, ticket));
  call Lval_Split(snoopPermissions, sp');
  dir[ma]->state  := if currRequest is Own then Owner(currRequest->i) else Sharers(Set_Add(Set_Singleton(dirState->i), currRequest->i));
  dir[ma]->currRequest := NoDirRequest();
  asyncCall := atomic_cache_read_resp(currRequest->i, ma, value, if currRequest is Own then Exclusive() else Shared(), ticket, drp', sp');
  call create_async(asyncCall);
}
yield procedure {:layer 2} dir_snoop_exclusive_resp(i: CacheId, ma: MemAddr, opt_value: Option Value, {:layer 1,2} {:linear_in} dp: Lset DirPermission, {:layer 1,2} {:linear_in} sp: Lval SnoopPermission)
refines atomic_dir_snoop_exclusive_resp;
{
  var dirInfo: DirInfo;
  var dirState: DirState;
  var currRequest: DirRequest;
  var value: Value;
  var ticket: int;
  var {:layer 1,2} drp: Lset DirRequestPermission;
  var sp': Lval SnoopPermission;
  if (opt_value is Some) {
    call write_mem(ma, opt_value->t, dp);
  }
  call dirInfo, drp := dir_snoop_exclusive_resp_begin(i, ma, dp, sp);
  dirState := dirInfo->state;
  assert {:layer 2} dirState is Owner;
  currRequest := dirInfo->currRequest;
  assert {:layer 2} !(currRequest is NoDirRequest);
  call value := read_mem(ma, dp);
  call ticket, sp' := increment_back(currRequest->i, ma, dp);
  dirState := if currRequest is Own then Owner(currRequest->i) else Sharers(Set_Add(Set_Singleton(dirState->i), currRequest->i));
  call dir_req_end(ma, dirState, dp);
  async call cache_read_resp(currRequest->i, ma, value, if currRequest is Own then Exclusive() else Shared(), ticket, drp, sp');
}

async atomic action {:layer 3} atomic_dir_snoop_shared_resp(i: CacheId, ma: MemAddr, {:linear_in} dpOne: Lset DirPermission, {:linear_in} sp: Lval SnoopPermission)
modifies dir, back, dirPermissions, snoopPermissions, dirRequestPermissionsAtDir;
creates atomic_cache_read_resp;
{
  var dirInfo: DirInfo;
  var dirState: DirState;
  var currRequest: DirRequest;
  var ticket: int;
  var value: Value;
  var drp': Lset DirRequestPermission;
  var sp': Lval SnoopPermission;
  var asyncCall: atomic_cache_read_resp;
  dirInfo := dir[ma];
  dirState := dirInfo->state;
  assert dirState is Sharers;
  assert Set_Contains(dirState->iset, i);
  currRequest := dirInfo->currRequest;
  assert currRequest is Own;
  call Lset_Transfer(dirPermissions, dpOne);
  call Lval_Transfer(snoopPermissions, sp);
  dirState->iset := Set_Remove(dirState->iset, i);
  if (dirState->iset != Set_Empty()) {
    dir[ma]->state := dirState;
    return;
  }
  value := mem[ma];
  ticket := back[currRequest->i][ma];
  back[currRequest->i][ma] := ticket + 1;
  drp' := Lset(MapOne(DirRequestPermission(currRequest->i, Hash(ma))));
  call Lset_Split(dirRequestPermissionsAtDir, drp');
  sp' := Lval(SnoopPermission(currRequest->i, ma, ticket));
  call Lval_Split(snoopPermissions, sp');
  dir[ma]->state  := Owner(currRequest->i);
  dir[ma]->currRequest := NoDirRequest();
  asyncCall := atomic_cache_read_resp(currRequest->i, ma, value, Exclusive(), ticket, drp', sp');
  call create_async(asyncCall);
}
yield procedure {:layer 2} dir_snoop_shared_resp(i: CacheId, ma: MemAddr, {:layer 1,2} {:linear_in} dpOne: Lset DirPermission, {:layer 1,2} {:linear_in} sp: Lval SnoopPermission)
refines atomic_dir_snoop_shared_resp;
{
  var dirInfo: DirInfo;
  var dirState: DirState;
  var currRequest: DirRequest;
  var value: Value;
  var ticket: int;
  var {:layer 1,2} drp: Lset DirRequestPermission;
  var {:layer 1,2} {:linear} dp: Lset DirPermission;
  var sp': Lval SnoopPermission;
  call dirInfo, drp, dp := dir_snoop_shared_resp_begin(i, ma, dpOne, sp);
  dirState := dirInfo->state;
  assert {:layer 2} dirState is Sharers;
  currRequest := dirInfo->currRequest;
  assert {:layer 2} currRequest is Own;
  if (dirState == Sharers(Set_Empty())) {
    call value := read_mem(ma, dp);
    call ticket, sp' := increment_back(currRequest->i, ma, dp);
    dirState := Owner(currRequest->i);
    call dir_req_end(ma, dirState, dp);
    async call cache_read_resp(currRequest->i, ma, value, Exclusive(), ticket, drp, sp');
  }
}

right action {:layer 2} atomic_dir_req_begin(ma: MemAddr, dirRequest: DirRequest, {:linear_in} drp: Lset DirRequestPermission)
returns (dirInfo: DirInfo, drp': Lset DirRequestPermission, dp: Lset DirPermission)
modifies back, dir, dirRequestPermissionsAtDir, dirPermissions;
{
  var dirState: DirState;
  assume {:add_to_pool "DirPermission", DirPermission(i0, ma)} true;
  call dirInfo := primitive_dir_req_begin(ma, dirRequest);
  call drp', dp, dirPermissions, dirRequestPermissionsAtDir := 
    dir_req_move_permissions(ma, dirRequest, dirInfo->state, drp, dirPermissions, dirRequestPermissionsAtDir);
}
yield procedure {:layer 1} dir_req_begin(ma: MemAddr, dirRequest: DirRequest, {:layer 1} {:linear_in} drp: Lset DirRequestPermission)
returns (dirInfo: DirInfo, {:layer 1} drp': Lset DirRequestPermission, {:layer 1} dp: Lset DirPermission)
refines atomic_dir_req_begin;
{
  call dirInfo := dir_req_begin#0(ma, dirRequest);
  call {:layer 1} drp', dp, dirPermissions, dirRequestPermissionsAtDir := 
    dir_req_move_permissions(ma, dirRequest, dirInfo->state, drp, dirPermissions, dirRequestPermissionsAtDir);
}

pure action dir_req_move_permissions(
  ma: MemAddr, 
  dirRequest: DirRequest, 
  dirState: DirState, 
  {:linear_in} drp: Lset DirRequestPermission,
  {:linear_in} dirPermissions: Lset DirPermission,
  {:linear_in} dirRequestPermissionsAtDir: Lset DirRequestPermission) 
  returns (
    drp': Lset DirRequestPermission,
    dp: Lset DirPermission,
    dirPermissions': Lset DirPermission,
    dirRequestPermissionsAtDir': Lset DirRequestPermission)
{
  drp', dirPermissions', dirRequestPermissionsAtDir' := drp, dirPermissions, dirRequestPermissionsAtDir;
  if ((dirRequest is Share && dirState is Owner) || (dirRequest is Own && dirState != Sharers(Set_Empty()))) {
    call Lset_Transfer(dirRequestPermissionsAtDir', drp');
    call drp' := Lset_Empty();
  }
  if (dirRequest is Own && dirState is Sharers && dirState->iset != Set_Empty()) {
    assume {:add_to_pool "DirPermission", DirPermission(Set_Choose(dirState->iset), ma)} true;
    dp := Lset((lambda x: DirPermission :: x->ma == ma && Set_Contains(dirState->iset, x->i)));
  } else {
    dp := WholeDirPermission(ma);
  }
  call Lset_Split(dirPermissions', dp);
}

atomic action {:layer 1} atomic_dir_req_begin#0(ma: MemAddr, dirRequest: DirRequest) returns (dirInfo: DirInfo)
modifies back, dir;
{
  call dirInfo := primitive_dir_req_begin(ma, dirRequest);
}
yield procedure {:layer 0} dir_req_begin#0(ma: MemAddr, dirRequest: DirRequest) returns (dirInfo: DirInfo);
refines atomic_dir_req_begin#0;

action {:layer 1,2} primitive_dir_req_begin(ma: MemAddr, dirRequest: DirRequest) returns (dirInfo: DirInfo)
modifies back, dir;
{
  assert !(dirRequest is NoDirRequest);
  assume dir[ma]->currRequest == NoDirRequest();
  dir[ma]->currRequest := dirRequest;
  dirInfo := dir[ma];
}

atomic action {:layer 2} atomic_dir_snoop_exclusive_resp_begin(i: CacheId, ma: MemAddr, dp: Lset DirPermission, {:linear_in} sp: Lval SnoopPermission) returns (dirInfo: DirInfo, drp: Lset DirRequestPermission)
modifies dir, dirRequestPermissionsAtDir, snoopPermissions;
{
  assert dp == WholeDirPermission(ma);
  assume {:add_to_pool "DirPermission", DirPermission(i0, ma)} true;
  call dirInfo := primitive_dir_snoop_resp_begin(i, ma);
  call drp, dirRequestPermissionsAtDir, snoopPermissions := 
    dir_snoop_exclusive_resp_move_permissions(ma, dirInfo, sp, dirRequestPermissionsAtDir, snoopPermissions);
}
yield procedure {:layer 1} dir_snoop_exclusive_resp_begin(i: CacheId, ma: MemAddr, {:layer 1} dp: Lset DirPermission, {:layer 1} {:linear_in} sp: Lval SnoopPermission) returns (dirInfo: DirInfo, {:layer 1} drp: Lset DirRequestPermission)
refines atomic_dir_snoop_exclusive_resp_begin;
{
  call dirInfo := dir_snoop_resp_begin#0(i, ma);
  call {:layer 1} drp, dirRequestPermissionsAtDir, snoopPermissions := 
    dir_snoop_exclusive_resp_move_permissions(ma, dirInfo, sp, dirRequestPermissionsAtDir, snoopPermissions);
}

pure action dir_snoop_exclusive_resp_move_permissions(
  ma: MemAddr,
  dirInfo: DirInfo,
  {:linear_in} sp: Lval SnoopPermission,
  {:linear_in} dirRequestPermissionsAtDir: Lset DirRequestPermission,
  {:linear_in} snoopPermissions: Lset SnoopPermission)
  returns (
    drp: Lset DirRequestPermission,
    dirRequestPermissionsAtDir': Lset DirRequestPermission,
    snoopPermissions': Lset SnoopPermission)
{
  dirRequestPermissionsAtDir', snoopPermissions' := dirRequestPermissionsAtDir, snoopPermissions;
  call Lval_Transfer(snoopPermissions', sp);
  drp := Lset(MapOne(DirRequestPermission(dirInfo->currRequest->i, Hash(ma))));
  call Lset_Split(dirRequestPermissionsAtDir', drp);
}

atomic action {:layer 2} atomic_dir_snoop_shared_resp_begin(i: CacheId, ma: MemAddr, {:linear_in} dpOne: Lset DirPermission, {:linear_in} sp: Lval SnoopPermission)
returns (dirInfo: DirInfo, drp: Lset DirRequestPermission, dp: Lset DirPermission)
modifies dir, dirRequestPermissionsAtDir, dirPermissions, snoopPermissions;
{
  assert Lset_Contains(dpOne, DirPermission(i, ma));
  call dirInfo := primitive_dir_snoop_resp_begin(i, ma);
  call drp, dp, dirPermissions, dirRequestPermissionsAtDir, snoopPermissions := 
    dir_snoop_shared_resp_move_permissions(ma, dirInfo, dpOne, sp, dirPermissions, dirRequestPermissionsAtDir, snoopPermissions);
}
yield procedure {:layer 1} dir_snoop_shared_resp_begin(i: CacheId, ma: MemAddr, {:layer 1} {:linear_in} dpOne: Lset DirPermission, {:layer 1} {:linear_in} sp: Lval SnoopPermission)
returns (dirInfo: DirInfo, {:layer 1} drp: Lset DirRequestPermission, {:layer 1} dp: Lset DirPermission)
refines atomic_dir_snoop_shared_resp_begin;
{
  call dirInfo := dir_snoop_resp_begin#0(i, ma);
  call {:layer 1} drp, dp, dirPermissions, dirRequestPermissionsAtDir, snoopPermissions := 
    dir_snoop_shared_resp_move_permissions(ma, dirInfo, dpOne, sp, dirPermissions, dirRequestPermissionsAtDir, snoopPermissions);
}

pure action dir_snoop_shared_resp_move_permissions(
  ma: MemAddr,
  dirInfo: DirInfo,
  {:linear_in} dpOne: Lset DirPermission, 
  {:linear_in} sp: Lval SnoopPermission, 
  {:linear_in} dirPermissions: Lset DirPermission,
  {:linear_in} dirRequestPermissionsAtDir: Lset DirRequestPermission,
  {:linear_in} snoopPermissions: Lset SnoopPermission)
  returns (
    drp: Lset DirRequestPermission, 
    dp: Lset DirPermission, 
    dirPermissions': Lset DirPermission, 
    dirRequestPermissionsAtDir': Lset DirRequestPermission, 
    snoopPermissions': Lset SnoopPermission)
{
  dirPermissions', dirRequestPermissionsAtDir', snoopPermissions' := dirPermissions, dirRequestPermissionsAtDir, snoopPermissions;
  call Lset_Transfer(dirPermissions', dpOne);
  call Lval_Transfer(snoopPermissions', sp);
  if (dirInfo->state == Sharers(Set_Empty())) {
    drp := Lset(MapOne(DirRequestPermission(dirInfo->currRequest->i, Hash(ma))));
    call Lset_Split(dirRequestPermissionsAtDir', drp);
    dp := WholeDirPermission(ma);
    call Lset_Split(dirPermissions', dp);
  } else {
    call drp := Lset_Empty();
    call dp := Lset_Empty();
  }
}

atomic action {:layer 1} atomic_dir_snoop_resp_begin#0(i: CacheId, ma: MemAddr) returns (dirInfo: DirInfo)
modifies dir;
{
  call dirInfo := primitive_dir_snoop_resp_begin(i, ma);
}
yield procedure {:layer 0} dir_snoop_resp_begin#0(i: CacheId, ma: MemAddr) returns (dirInfo: DirInfo);
refines atomic_dir_snoop_resp_begin#0;

action {:layer 1,2} primitive_dir_snoop_resp_begin(i: CacheId, ma: MemAddr) returns (dirInfo: DirInfo)
modifies dir;
{
  if (dir[ma]->state is Sharers) {
    assert Set_Contains(dir[ma]->state->iset, i);
    dir[ma]->state->iset := Set_Remove(dir[ma]->state->iset, i);
  } else {
    assert i == dir[ma]->state->i;
  }
  dirInfo := dir[ma];
}

left action {:layer 2} atomic_dir_req_end(ma: MemAddr, dirState: DirState, {:linear_in} dp: Lset DirPermission)
modifies dir, dirPermissions;
{
  assert dp == WholeDirPermission(ma);
  assume {:add_to_pool "DirPermission", DirPermission(i0, ma)} true;
  call primitive_dir_req_end(ma, dirState);
  call Lset_Transfer(dirPermissions, dp);
}
yield procedure {:layer 1} dir_req_end(ma: MemAddr, dirState: DirState, {:layer 1} {:linear_in} dp: Lset DirPermission)
refines atomic_dir_req_end;
{
  call dir_req_end#0(ma, dirState);
  call {:layer 1} Lset_Transfer(dirPermissions, dp);
}

atomic action {:layer 1} atomic_dir_req_end#0(ma: MemAddr, dirState: DirState)
modifies dir;
{
  call primitive_dir_req_end(ma, dirState);
}
yield procedure {:layer 0} dir_req_end#0(ma: MemAddr, dirState: DirState);
refines atomic_dir_req_end#0;

action {:layer 1,2} primitive_dir_req_end(ma: MemAddr, dirState: DirState)
modifies dir;
{
  assert !(dir[ma]->currRequest is NoDirRequest);
  dir[ma]->state := dirState;
  dir[ma]->currRequest := NoDirRequest();
}


// Atomic actions for channels and memory
both action {:layer 2} atomic_read_back(i: CacheId, ma: MemAddr, dp: Lset DirPermission) returns (ticket: int, sp: Lval SnoopPermission)
modifies snoopPermissions;
{
  assert Lset_Contains(dp, DirPermission(i, ma));
  ticket := back[i][ma];
  sp := Lval(SnoopPermission(i, ma, ticket));
  call Lval_Split(snoopPermissions, sp);
}
yield procedure {:layer 1} read_back(i: CacheId, ma: MemAddr, {:layer 1} dp: Lset DirPermission) returns (ticket: int, sp: Lval SnoopPermission)
refines atomic_read_back;
{
  call ticket := read_back#0(i, ma);
  sp := Lval(SnoopPermission(i, ma, ticket));
  call {:layer 1} Lval_Split(snoopPermissions, sp);
}

atomic action {:layer 1} atomic_read_back#0(i: CacheId, ma: MemAddr) returns (ticket: int)
{
  ticket := back[i][ma];
}
yield procedure {:layer 0} read_back#0(i: CacheId, ma: MemAddr) returns (ticket: int);
refines atomic_read_back#0;

both action {:layer 2} atomic_increment_back(i: CacheId, ma: MemAddr, dp: Lset DirPermission) returns (ticket: int, sp: Lval SnoopPermission)
modifies back, snoopPermissions;
{
  assert dp == WholeDirPermission(ma);
  assume {:add_to_pool "DirPermission", DirPermission(i0, ma)} true;
  ticket := back[i][ma];
  back[i][ma] := back[i][ma] + 1;
  sp := Lval(SnoopPermission(i, ma, ticket));
  call Lval_Split(snoopPermissions, sp);
}
yield procedure {:layer 1} increment_back(i: CacheId, ma: MemAddr, {:layer 1} dp: Lset DirPermission) returns (ticket: int, sp: Lval SnoopPermission)
refines atomic_increment_back;
{
  call ticket := increment_back#0(i, ma);
  sp := Lval(SnoopPermission(i, ma, ticket));
  call {:layer 1} Lval_Split(snoopPermissions, sp);
}

atomic action {:layer 1} atomic_increment_back#0(i: CacheId, ma: MemAddr) returns (ticket: int)
modifies back;
{
  ticket := back[i][ma];
  back[i][ma] := back[i][ma] + 1;
}
yield procedure {:layer 0} increment_back#0(i: CacheId, ma: MemAddr) returns (ticket: int);
refines atomic_increment_back#0;

right action {:layer 2} atomic_wait_front(i: CacheId, ma: MemAddr, ticket: int)
{
  assume ticket <= front[i][ma];
}
yield procedure {:layer 1} wait_front(i: CacheId, ma: MemAddr, ticket: int)
refines atomic_wait_front;
{
  call wait_front#0(i, ma, ticket);
}

atomic action {:layer 1} atomic_wait_front#0(i: CacheId, ma: MemAddr, ticket: int)
{
  assume ticket == front[i][ma];
}
yield procedure {:layer 0} wait_front#0(i: CacheId, ma: MemAddr, ticket: int);

left action {:layer 2} atomic_increment_front(i: CacheId, ma: MemAddr)
modifies front;
{
  front[i][ma] := front[i][ma] + 1;
}
yield procedure {:layer 1} increment_front(i: CacheId, ma: MemAddr)
refines atomic_increment_front;
{
  call increment_front#0(i, ma);
}

atomic action {:layer 1} atomic_increment_front#0(i: CacheId, ma: MemAddr)
modifies front;
{
  front[i][ma] := front[i][ma] + 1;
}
yield procedure {:layer 0} increment_front#0(i: CacheId, ma: MemAddr);
refines atomic_increment_front#0;

both action {:layer 2} atomic_read_mem(ma: MemAddr, dp: Lset DirPermission) returns (value: Value)
{
  assert dp == WholeDirPermission(ma);
  assume {:add_to_pool "DirPermission", DirPermission(i0, ma)} true;
  value := mem[ma];
}
yield procedure {:layer 1} read_mem(ma: MemAddr, {:layer 1} dp: Lset DirPermission) returns (value: Value)
refines atomic_read_mem;
{
  call value := read_mem#0(ma);
}

atomic action {:layer 1} atomic_read_mem#0(ma: MemAddr) returns (value: Value)
{
  value := mem[ma];
}
yield procedure {:layer 0} read_mem#0(ma: MemAddr) returns (value: Value);
refines atomic_read_mem#0;

both action {:layer 2} atomic_write_mem(ma: MemAddr, value: Value, dp: Lset DirPermission)
modifies mem;
{
  assert dp == WholeDirPermission(ma);
  assume {:add_to_pool "DirPermission", DirPermission(i0, ma)} true;
  mem[ma] := value;
}
yield procedure {:layer 1} write_mem(ma: MemAddr, value: Value, {:layer 1} dp: Lset DirPermission)
refines atomic_write_mem;
{
  call write_mem#0(ma, value);
}

atomic action {:layer 1} atomic_write_mem#0(ma: MemAddr, value: Value)
modifies mem;
{
  mem[ma] := value;
}
yield procedure {:layer 0} write_mem#0(ma: MemAddr, value: Value);
refines atomic_write_mem#0;
