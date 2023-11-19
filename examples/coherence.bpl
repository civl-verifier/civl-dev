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
  DirRequestPermission(i: CacheId, ma: MemAddr)
}

datatype DirPermission {
  DirPermission(i: CacheId, ma: MemAddr)
}

function {:inline} WholeDirPermission(ma: MemAddr): Lset DirPermission {
  Lset((lambda x: DirPermission :: x->ma == ma))
}

datatype SnoopPermission {
  SnoopPermission(i: CacheId, ma: MemAddr, ticket: int)
}

var {:layer 0,2} mem: [MemAddr]Value;
var {:layer 0,2} dir: [MemAddr]DirInfo;
var {:layer 0,2} cache: [CacheId]Cache;

var {:layer 0,2} front: [CacheId][MemAddr]int;
var {:layer 0,2} back: [CacheId][MemAddr]int;

var {:layer 1,2} dirRequestPermissionsAtCache: Lset DirRequestPermission;
var {:layer 1,2} dirRequestPermissionsAtDir: Lset DirRequestPermission;
var {:layer 1,2} snoopPermissions: Lset SnoopPermission;
var {:layer 1,2} dirPermissions: Lset DirPermission;


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
    // cache[i][ma]->currRequest was set to this request
    if (line->state == Invalid()) {
      async call dir_read_share_req(i, ma, drp);
    } else if (line->state == Modified()) {
      async call dir_evict_req(i, ma, Some(line->value), drp);
    } else {
      async call dir_evict_req(i, ma, None(), drp);
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
    // cache[i][ma]->currRequest was set to this request
    if (line->state == Invalid() || line->ma == ma) {
      async call dir_read_own_req(i, ma, drp);
    } else if (line->state == Modified()) {
      async call dir_evict_req(i, ma, Some(line->value), drp);
    } else {
      async call dir_evict_req(i, ma, None(), drp);
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
    // cache[i][ma]->currRequest was set to this request
    if (line->state == Invalid() || line->ma == ma) {
      async call dir_read_own_req(i, ma, drp);
    } else if (line->state == Modified()) {
      async call dir_evict_req(i, ma, Some(line->value), drp);
    } else {
      async call dir_evict_req(i, ma, None(), drp);
    }
  }
}

atomic action {:layer 2} atomic_cache_req_begin(i: CacheId, currRequest: CacheRequest) returns (result: Option Value, line: CacheLine, drp: Lset DirRequestPermission)
modifies cache, dirRequestPermissionsAtCache;
{
  call result, line := atomic_cache_req_begin#0(i, currRequest);
  if (result is None && line->currRequest is NoCacheRequest) {
    drp := Lset(MapOne(DirRequestPermission(i, currRequest->ma)));
    call Lset_Split(drp, dirRequestPermissionsAtCache);
  } else {
    call drp := Lset_Empty();
  }
}
yield procedure {:layer 1} cache_req_begin(i: CacheId, currRequest: CacheRequest) returns (result: Option Value, line: CacheLine, {:layer 1} drp: Lset DirRequestPermission)
refines atomic_cache_req_begin;
{
  call result, line := cache_req_begin#0(i, currRequest);
  if (result is None && line->currRequest is NoCacheRequest) {
    drp := Lset(MapOne(DirRequestPermission(i, currRequest->ma)));
    call {:layer 1} Lset_Split(drp, dirRequestPermissionsAtCache);
  } else {
    call {:layer 1} drp := Lset_Empty();
  }
}

atomic action {:layer 1,2} atomic_cache_req_begin#0(i: CacheId, currRequest: CacheRequest) returns (result: Option Value, line: CacheLine)
modifies cache;
{
  var ca: CacheAddr;
  var ma: MemAddr;
  assert !(currRequest is NoCacheRequest);
  ma := currRequest->ma;
  ca := Hash(ma);
  line := cache[i][ca];
  result := None();
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
yield procedure {:layer 0} cache_req_begin#0(i: CacheId, currRequest: CacheRequest) returns (result: Option Value, line: CacheLine);
refines atomic_cache_req_begin#0;

yield procedure {:layer 2} cache_read_resp(i: CacheId, ma: MemAddr, v: Value, s: State, ticket: int, {:layer 1,2} {:linear_in} drp: Lset DirRequestPermission, {:layer 1,2} {:linear_in} sp: Lval SnoopPermission)
{
  call increment_front(i, ma, ticket, drp);
  call cache_read_resp_begin(i, ma, v, s, drp, sp);
}

atomic action {:layer 2} atomic_cache_read_resp_begin(i: CacheId, ma: MemAddr, v: Value, s: State, {:linear_in} drp: Lset DirRequestPermission, {:linear_in} sp: Lval SnoopPermission)
modifies cache, front, dirRequestPermissionsAtCache;
{
  call atomic_cache_read_resp_begin#0(i, ma, v, s);
  call Lset_Transfer(drp, dirRequestPermissionsAtCache);
}
yield procedure {:layer 1} cache_read_resp_begin(i: CacheId, ma: MemAddr, v: Value, s: State, {:layer 1} {:linear_in} drp: Lset DirRequestPermission, {:layer 1} {:linear_in} sp: Lval SnoopPermission)
refines atomic_cache_read_resp_begin;
{
  call cache_read_resp_begin#0(i, ma, v, s);
  call {:layer 1} Lset_Transfer(drp, dirRequestPermissionsAtCache);
}

atomic action {:layer 1,2} atomic_cache_read_resp_begin#0(i: CacheId, ma: MemAddr, v: Value, s: State)
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
yield procedure {:layer 0} cache_read_resp_begin#0(i: CacheId, ma: MemAddr, v: Value, s: State);
refines atomic_cache_read_resp_begin#0;

yield procedure {:layer 2} cache_evict_resp(i: CacheId, ma: MemAddr, ticket: int, {:layer 1,2} {:linear_in} drp: Lset DirRequestPermission, {:layer 1,2} {:linear_in} sp: Lval SnoopPermission)
{
  var currRequest: CacheRequest;
  call increment_front(i, ma, ticket, drp);
  call currRequest := cache_evict_resp_begin(i, ma, sp);
  if (currRequest is ReadShared) {
    async call dir_read_share_req(i, currRequest->ma, drp);
  } else {
    async call dir_read_own_req(i, currRequest->ma, drp);
  }
}

atomic action {:layer 2} atomic_cache_evict_resp_begin(i: CacheId, ma: MemAddr, {:linear_in} sp: Lval SnoopPermission) returns (currRequest: CacheRequest)
modifies cache;
{
  call currRequest := atomic_cache_evict_resp_begin#0(i, ma);
}
yield procedure {:layer 1} cache_evict_resp_begin(i: CacheId, ma: MemAddr, {:layer 1} {:linear_in} sp: Lval SnoopPermission) returns (currRequest: CacheRequest)
refines atomic_cache_evict_resp_begin;
{
  call currRequest := cache_evict_resp_begin#0(i, ma);
}

atomic action {:layer 1,2} atomic_cache_evict_resp_begin#0(i: CacheId, ma: MemAddr) returns (currRequest: CacheRequest)
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
yield procedure {:layer 0} cache_evict_resp_begin#0(i: CacheId, ma: MemAddr) returns (currRequest: CacheRequest);
refines atomic_cache_evict_resp_begin#0;

yield procedure {:layer 2} cache_snoop_exclusive_req(i: CacheId, ma: MemAddr, s: State, ticket: int, {:layer 1,2} {:linear_in} dp: Lset DirPermission, {:layer 1,2} {:linear_in} sp: Lval SnoopPermission)
{
  var opt_value: Option Value;
  call opt_value := cache_snoop_exclusive_req_begin(i, ma, s, ticket, dp);
  async call dir_snoop_exclusive_resp(i, ma, opt_value, dp, sp);
}

atomic action {:layer 2} atomic_cache_snoop_exclusive_req_begin(i: CacheId, ma: MemAddr, s: State, ticket: int, {:layer 1} {:linear} dp: Lset DirPermission) returns (opt_value: Option Value)
modifies cache;
{
  call opt_value := atomic_cache_snoop_exclusive_req_begin#0(i, ma, s, ticket);
}
yield procedure {:layer 1} cache_snoop_exclusive_req_begin(i: CacheId, ma: MemAddr, s: State, ticket: int, {:layer 1} {:linear} dp: Lset DirPermission) returns (opt_value: Option Value)
refines atomic_cache_snoop_exclusive_req_begin;
{
  call opt_value := cache_snoop_exclusive_req_begin#0(i, ma, s, ticket);
}

atomic action {:layer 1,2} atomic_cache_snoop_exclusive_req_begin#0(i: CacheId, ma: MemAddr, s: State, ticket: int) returns (opt_value: Option Value)
modifies cache;
{
  var ca: CacheAddr;
  var line: CacheLine;
  assume ticket == front[i][ma];
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
yield procedure {:layer 0} cache_snoop_exclusive_req_begin#0(i: CacheId, ma: MemAddr, s: State, ticket: int) returns (opt_value: Option Value);
refines atomic_cache_snoop_exclusive_req_begin#0;

yield procedure {:layer 2} cache_snoop_shared_req(i: CacheId, ma: MemAddr, ticket: int, {:layer 1,2} {:linear_in} dpOne: Lset DirPermission, {:layer 1,2} {:linear_in} sp: Lval SnoopPermission)
{
  call cache_snoop_shared_req_begin(i, ma, ticket, dpOne);
  async call dir_snoop_shared_resp(i, ma, dpOne, sp);
}

atomic action {:layer 2} atomic_cache_snoop_shared_req_begin(i: CacheId, ma: MemAddr, ticket: int, {:linear} dpOne: Lset DirPermission)
modifies cache;
{
  call atomic_cache_snoop_shared_req_begin#0(i, ma, ticket);
}
yield procedure {:layer 1} cache_snoop_shared_req_begin(i: CacheId, ma: MemAddr, ticket: int, {:layer 1} {:linear} dpOne: Lset DirPermission)
refines atomic_cache_snoop_shared_req_begin;
{
  call cache_snoop_shared_req_begin#0(i, ma, ticket);
}

atomic action {:layer 1,2} atomic_cache_snoop_shared_req_begin#0(i: CacheId, ma: MemAddr, ticket: int)
modifies cache;
{
  var ca: CacheAddr;
  var line: CacheLine;
  assume ticket == front[i][ma];
  ca := Hash(ma);
  line := cache[i][ca];
  assert line->ma == ma;
  assert line->state == Shared();
  cache[i][ca]->state := Invalid();
}
yield procedure {:layer 0} cache_snoop_shared_req_begin#0(i: CacheId, ma: MemAddr, ticket: int);
refines atomic_cache_snoop_shared_req_begin#0;


// at dir
yield procedure {:layer 2} dir_read_share_req(i: CacheId, ma: MemAddr, {:layer 1,2} {:linear_in} drp: Lset DirRequestPermission)
{
  var dirInfo: DirInfo;
  var dirState: DirState;
  var {:layer 1,2} drp': Lset DirRequestPermission;
  var {:layer 1,2} dp: Lset DirPermission;
  call dirInfo, drp', dp := dir_req_begin(ma, Share(i), drp);
  dirState := dirInfo->state;
  if (dirState is Owner) {
    call dir_snoop_exclusive_victim(ma, dirState->i, Shared(), dp);
  } else {
    call dir_read_req_middle(i, ma, dirState, drp', dp);
  }
}

yield procedure {:layer 2} dir_read_own_req(i: CacheId, ma: MemAddr, {:layer 1,2} {:linear_in} drp: Lset DirRequestPermission)
{
  var dirInfo: DirInfo;
  var dirState: DirState;
  var {:layer 1,2} drp': Lset DirRequestPermission;
  var {:layer 1,2} dp: Lset DirPermission;
  call dirInfo, drp', dp := dir_req_begin(ma, Own(i), drp);
  dirState := dirInfo->state;
  if (dirState is Owner) {
    call dir_snoop_exclusive_victim(ma, dirState->i, Invalid(), dp);
  } else if (dirState == Sharers(Set_Empty())) {
    call dir_read_req_middle(i, ma, dirState, drp', dp);
  } else {
    call dir_snoop_shared_victims(ma, dirState->iset, dp);
  }
}

yield procedure {:layer 2} dir_evict_req(i: CacheId, ma: MemAddr, opt_value: Option Value, {:layer 1,2} {:linear_in} drp: Lset DirRequestPermission)
{
  var dirInfo: DirInfo;
  var dirState: DirState;
  var {:layer 1,2} drp': Lset DirRequestPermission;
  var {:layer 1,2} dp: Lset DirPermission;
  call dirInfo, drp', dp := dir_req_begin(ma, Evict(i), drp);
  if (opt_value is Some) {
    call write_mem(ma, opt_value->t, dp);
  }
  dirState := dirInfo->state;
  call dir_evict_req_middle(i, ma, dirState, drp', dp);
}

yield procedure {:layer 2} dir_snoop_exclusive_resp(i: CacheId, ma: MemAddr, opt_value: Option Value, {:layer 1,2} {:linear_in} dp: Lset DirPermission, {:layer 1,2} {:linear_in} sp: Lval SnoopPermission)
{
  var dirInfo: DirInfo;
  var {:layer 1,2} drp: Lset DirRequestPermission;
  if (opt_value is Some) {
    call write_mem(ma, opt_value->t, dp);
  }
  call dirInfo, drp := dir_snoop_exclusive_resp_begin(i, ma, sp);
  call dir_snoop_resp_middle(ma, dirInfo, drp, dp);
}

yield procedure {:layer 2} dir_snoop_shared_resp(i: CacheId, ma: MemAddr, {:layer 1,2} {:linear_in} dpOne: Lset DirPermission, {:layer 1,2} {:linear_in} sp: Lval SnoopPermission)
{
  var dirInfo: DirInfo;
  var {:layer 1,2} drp: Lset DirRequestPermission;
  var {:layer 1,2} {:linear} dp: Lset DirPermission;
  call dirInfo, drp, dp := dir_snoop_shared_resp_begin(i, ma, dpOne, sp);
  call dir_snoop_resp_middle(ma, dirInfo, drp, dp);
}

atomic action {:layer 2} atomic_dir_req_begin(ma: MemAddr, dirRequest: DirRequest, {:linear_in} drp: Lset DirRequestPermission)
returns (dirInfo: DirInfo, drp': Lset DirRequestPermission, dp: Lset DirPermission)
modifies back, dir, dirRequestPermissionsAtDir, dirPermissions;
{
  var dirState: DirState;
  call dirInfo := atomic_dir_req_begin#0(ma, dirRequest);
  dirState := dirInfo->state;
  drp' := drp;
  if ((dirRequest is Share && dirState is Owner) || (dirRequest is Own && dirState != Sharers(Set_Empty()))) {
    call Lset_Transfer(drp', dirRequestPermissionsAtDir);
    call drp' := Lset_Empty();
  }
  if (dirRequest is Own && dirState is Sharers && dirState->iset != Set_Empty()) {
    dp := Lset((lambda x: DirPermission :: x->ma == ma && Set_Contains(dirState->iset, x->i)));
    call Lset_Split(dp, dirPermissions);
  } else {
    dp := WholeDirPermission(ma);
    call Lset_Split(dp, dirPermissions);
  }
}
yield procedure {:layer 1} dir_req_begin(ma: MemAddr, dirRequest: DirRequest, {:layer 1} {:linear_in} drp: Lset DirRequestPermission)
returns (dirInfo: DirInfo, {:layer 1} drp': Lset DirRequestPermission, {:layer 1} dp: Lset DirPermission)
refines atomic_dir_req_begin;
{
  var dirState: DirState;
  call dirInfo := dir_req_begin#0(ma, dirRequest);
  dirState := dirInfo->state;
  drp' := drp;
  if ((dirRequest is Share && dirState is Owner) || (dirRequest is Own && dirState != Sharers(Set_Empty()))) {
    call {:layer 1} Lset_Transfer(drp', dirRequestPermissionsAtDir);
    call {:layer 1} drp' := Lset_Empty();
  }
  if (dirRequest is Own && dirState is Sharers && dirState->iset != Set_Empty()) {
    dp := Lset((lambda x: DirPermission :: x->ma == ma && Set_Contains(dirState->iset, x->i)));
    call {:layer 1} Lset_Split(dp, dirPermissions);
  } else {
    dp := WholeDirPermission(ma);
    call {:layer 1} Lset_Split(dp, dirPermissions);
  }
}

atomic action {:layer 1,2} atomic_dir_req_begin#0(ma: MemAddr, dirRequest: DirRequest) returns (dirInfo: DirInfo)
modifies back, dir;
{
  assume dir[ma]->currRequest == NoDirRequest();
  dir[ma]->currRequest := dirRequest;
  dirInfo := dir[ma];
}
yield procedure {:layer 0} dir_req_begin#0(ma: MemAddr, dirRequest: DirRequest) returns (dirInfo: DirInfo);
refines atomic_dir_req_begin#0;

yield procedure {:layer 2} dir_snoop_exclusive_victim(ma: MemAddr, victim: CacheId, state: State, {:layer 1,2} {:linear_in} dp: Lset DirPermission)
{
  var ticket: int;
  var {:layer 1,2} sp: Lval SnoopPermission;
  call ticket, sp := read_back(victim, ma, dp);
  async call cache_snoop_exclusive_req(victim, ma, state, ticket, dp, sp);
}

yield procedure {:layer 2} dir_snoop_shared_victims(ma: MemAddr, victims: Set CacheId, {:layer 1,2} {:linear_in} dp: Lset DirPermission)
{
  var victims': Set CacheId;
  var victim: CacheId;
  var ticket: int;
  var {:layer 1,2} dp': Lset DirPermission;
  var {:layer 1,2} dpOne: Lset DirPermission;
  var {:layer 1,2} sp: Lval SnoopPermission;
  victims' := victims;
  dp' := dp;
  while (victims' != Set_Empty()) {
    victim := Set_Choose(victims');
    victims' := Set_Remove(victims', victim);
    dpOne := Lset(MapOne(DirPermission(victim, ma)));
    call {:layer 1,2} Lset_Split(dpOne, dp');
    call ticket, sp := read_back(victim, ma, dpOne);
    async call cache_snoop_shared_req(victim, ma, ticket, dpOne, sp);
  }
}

yield procedure {:layer 2} dir_read_req_middle(i: CacheId, ma: MemAddr, dirState: DirState, {:layer 1,2} {:linear_in} drp: Lset DirRequestPermission, {:layer 1,2} {:linear_in} dp: Lset DirPermission)
{
  var dirState': DirState;
  var ticket: int;
  var value: Value;
  var {:layer 1,2} sp: Lval SnoopPermission;
  call value := read_mem(ma, dp);
  call ticket, sp := increment_back(i, ma, dp);
  if (dirState->iset == Set_Empty()) {
    dirState' := Owner(i);
    async call cache_read_resp(i, ma, value, Exclusive(), ticket, drp, sp);
  } else {
    dirState' := Sharers(Set_Add(dirState->iset, i));
    async call cache_read_resp(i, ma, value, Shared(), ticket, drp, sp);
  }
  call dir_req_end(ma, dirState', dp);
}

yield procedure {:layer 2} dir_evict_req_middle(i: CacheId, ma: MemAddr, dirState: DirState, {:layer 1,2} {:linear_in} drp: Lset DirRequestPermission, {:layer 1,2} {:linear_in} dp: Lset DirPermission)
{
  var dirState': DirState;
  var ticket: int;
  var {:layer 1,2} sp: Lval SnoopPermission;
  call ticket, sp := increment_back(i, ma, dp);
  async call cache_evict_resp(i, ma, ticket, drp, sp);
  if (dirState is Owner) {
    dirState' := Sharers(Set_Empty());
  } else {
    dirState' := Sharers(Set_Remove(dirState->iset, i));
  }
  call dir_req_end(ma, dirState', dp);
}

atomic action {:layer 2} atomic_dir_snoop_exclusive_resp_begin(i: CacheId, ma: MemAddr, {:linear_in} sp: Lval SnoopPermission) returns (dirInfo: DirInfo, drp: Lset DirRequestPermission)
modifies dir, dirRequestPermissionsAtDir, snoopPermissions;
{
  call dirInfo := atomic_dir_snoop_resp_begin#0(i, ma);
  call Lval_Transfer(sp, snoopPermissions);
  drp := Lset(MapOne(DirRequestPermission(dirInfo->currRequest->i, ma)));
  call Lset_Split(drp, dirRequestPermissionsAtDir);
}
yield procedure {:layer 1} dir_snoop_exclusive_resp_begin(i: CacheId, ma: MemAddr, {:layer 1} {:linear_in} sp: Lval SnoopPermission) returns (dirInfo: DirInfo, {:layer 1} drp: Lset DirRequestPermission)
refines atomic_dir_snoop_exclusive_resp_begin;
{
  call dirInfo := dir_snoop_resp_begin#0(i, ma);
  call {:layer 1} Lval_Transfer(sp, snoopPermissions);
  drp := Lset(MapOne(DirRequestPermission(dirInfo->currRequest->i, ma)));
  call {:layer 1} Lset_Split(drp, dirRequestPermissionsAtDir);
}

atomic action {:layer 2} atomic_dir_snoop_shared_resp_begin(i: CacheId, ma: MemAddr, {:linear_in} dpOne: Lset DirPermission, {:linear_in} sp: Lval SnoopPermission) 
returns (dirInfo: DirInfo, drp: Lset DirRequestPermission, dp: Lset DirPermission)
modifies dir, dirRequestPermissionsAtDir, dirPermissions, snoopPermissions;
{
  call dirInfo := atomic_dir_snoop_resp_begin#0(i, ma);
  call Lset_Transfer(dpOne, dirPermissions);
  call Lval_Transfer(sp, snoopPermissions);
  if (dirInfo->state == Sharers(Set_Empty())) {
    drp := Lset(MapOne(DirRequestPermission(dirInfo->currRequest->i, ma)));
    call Lset_Split(drp, dirRequestPermissionsAtDir);
    dp := WholeDirPermission(ma);
    call Lset_Split(dp, dirPermissions);
  } else {
    call drp := Lset_Empty();
    call dp := Lset_Empty();
  }
}
yield procedure {:layer 1} dir_snoop_shared_resp_begin(i: CacheId, ma: MemAddr, {:layer 1} {:linear_in} dpOne: Lset DirPermission, {:layer 1} {:linear_in} sp: Lval SnoopPermission) 
returns (dirInfo: DirInfo, {:layer 1} drp: Lset DirRequestPermission, {:layer 1} dp: Lset DirPermission)
refines atomic_dir_snoop_shared_resp_begin;
{
  call dirInfo := dir_snoop_resp_begin#0(i, ma);
  call {:layer 1} Lset_Transfer(dpOne, dirPermissions);
  call {:layer 1} Lval_Transfer(sp, snoopPermissions);
  if (dirInfo->state == Sharers(Set_Empty())) {
    drp := Lset(MapOne(DirRequestPermission(dirInfo->currRequest->i, ma)));
    call {:layer 1} Lset_Split(drp, dirRequestPermissionsAtDir);
    dp := WholeDirPermission(ma);
    call {:layer 1} Lset_Split(dp, dirPermissions);
  } else {
    call {:layer 1} drp := Lset_Empty();
    call {:layer 1} dp := Lset_Empty();
  }
}

atomic action {:layer 1,2} atomic_dir_snoop_resp_begin#0(i: CacheId, ma: MemAddr) returns (dirInfo: DirInfo)
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
yield procedure {:layer 0} dir_snoop_resp_begin#0(i: CacheId, ma: MemAddr) returns (dirInfo: DirInfo);
refines atomic_dir_snoop_resp_begin#0;

yield procedure {:layer 2} dir_snoop_resp_middle(ma: MemAddr, dirInfo: DirInfo, {:layer 1,2} {:linear_in} drp: Lset DirRequestPermission, {:layer 1,2} {:linear_in} dp: Lset DirPermission)
{
  var dirState: DirState;
  var currRequest: DirRequest;
  var ticket: int;
  var value: Value;
  var {:layer 1,2} sp: Lval SnoopPermission;
  dirState := dirInfo->state;
  currRequest := dirInfo->currRequest;
  if (dirState is Owner || dirState == Sharers(Set_Empty())) {
    call value := read_mem(ma, dp);
    call ticket, sp := increment_back(currRequest->i, ma, dp);
    if (currRequest is Own) {
      async call cache_read_resp(currRequest->i, ma, value, Exclusive(), ticket, drp, sp);
      dirState := Owner(dirInfo->currRequest->i);
    } else {
      async call cache_read_resp(currRequest->i, ma, value, Shared(), ticket, drp, sp);
      dirState := Sharers(Set_Add(Set_Singleton(dirState->i), currRequest->i));
    }
    call dir_req_end(ma, dirState, dp);
  }
}

atomic action {:layer 2} atomic_dir_req_end(ma: MemAddr, dirState: DirState, {:linear_in} dp: Lset DirPermission)
modifies dir, dirPermissions;
{
  call atomic_dir_req_end#0(ma, dirState);
  call Lset_Transfer(dp, dirPermissions);
}
yield procedure {:layer 1} dir_req_end(ma: MemAddr, dirState: DirState, {:layer 1} {:linear_in} dp: Lset DirPermission)
refines atomic_dir_req_end;
{
  call dir_req_end#0(ma, dirState);
  call {:layer 1} Lset_Transfer(dp, dirPermissions);
}

atomic action {:layer 1,2} atomic_dir_req_end#0(ma: MemAddr, dirState: DirState)
modifies dir;
{
  assert !(dir[ma]->currRequest is NoDirRequest);
  dir[ma]->state := dirState;
  dir[ma]->currRequest := NoDirRequest();
}
yield procedure {:layer 0} dir_req_end#0(ma: MemAddr, dirState: DirState);
refines atomic_dir_req_end#0;


// Atomic actions for channels and memory
atomic action {:layer 2} atomic_read_back(i: CacheId, ma: MemAddr, dp: Lset DirPermission) returns (ticket: int, sp: Lval SnoopPermission)
modifies snoopPermissions;
{
  assert Lset_Contains(dp, DirPermission(i, ma));
  call ticket := atomic_read_back#0(i, ma);
  sp := Lval(SnoopPermission(i, ma, ticket));
  call Lval_Split(sp, snoopPermissions);
}
yield procedure {:layer 1} read_back(i: CacheId, ma: MemAddr, {:layer 1} dp: Lset DirPermission) returns (ticket: int, sp: Lval SnoopPermission)
refines atomic_read_back;
{
  call ticket := read_back#0(i, ma);
  sp := Lval(SnoopPermission(i, ma, ticket));
  call {:layer 1} Lval_Split(sp, snoopPermissions);
}

atomic action {:layer 1,2} atomic_read_back#0(i: CacheId, ma: MemAddr) returns (ticket: int)
{
  ticket := back[i][ma];
}
yield procedure {:layer 0} read_back#0(i: CacheId, ma: MemAddr) returns (ticket: int);
refines atomic_read_back#0;

atomic action {:layer 2} atomic_increment_back(i: CacheId, ma: MemAddr, dp: Lset DirPermission) returns (ticket: int, sp: Lval SnoopPermission)
modifies back, snoopPermissions;
{
  assert dp == WholeDirPermission(ma);
  call ticket := atomic_increment_back#0(i, ma);
  sp := Lval(SnoopPermission(i, ma, ticket));
  call Lval_Split(sp, snoopPermissions);
}
yield procedure {:layer 1} increment_back(i: CacheId, ma: MemAddr, {:layer 1} dp: Lset DirPermission) returns (ticket: int, sp: Lval SnoopPermission)
refines atomic_increment_back;
{
  call ticket := increment_back#0(i, ma);
  sp := Lval(SnoopPermission(i, ma, ticket));
  call {:layer 1} Lval_Split(sp, snoopPermissions);
}

atomic action {:layer 1,2} atomic_increment_back#0(i: CacheId, ma: MemAddr) returns (ticket: int)
modifies back;
{
  ticket := back[i][ma];
  back[i][ma] := back[i][ma] + 1;
}
yield procedure {:layer 0} increment_back#0(i: CacheId, ma: MemAddr) returns (ticket: int);
refines atomic_increment_back#0;

atomic action {:layer 1,2} atomic_wait_front(i: CacheId, ma: MemAddr, ticket: int)
{
  assume ticket <= front[i][ma];
}
yield procedure {:layer 0} wait_front(i: CacheId, ma: MemAddr, ticket: int);

atomic action {:layer 2} atomic_increment_front(i: CacheId, ma: MemAddr, ticket: int, drp: Lset DirRequestPermission)
modifies front;
{
  assert Lset_Contains(drp, DirRequestPermission(i, ma));
  call atomic_increment_front#0(i, ma, ticket);
}
yield procedure {:layer 1} increment_front(i: CacheId, ma: MemAddr, ticket: int, {:layer 1} drp: Lset DirRequestPermission)
refines atomic_increment_front;
{
  call increment_front#0(i, ma, ticket);
}

atomic action {:layer 1,2} atomic_increment_front#0(i: CacheId, ma: MemAddr, ticket: int)
modifies front;
{
  assume ticket == front[i][ma];
  front[i][ma] := front[i][ma] + 1;
}
yield procedure {:layer 0} increment_front#0(i: CacheId, ma: MemAddr, ticket: int);
refines atomic_increment_front#0;

atomic action {:layer 2} atomic_read_mem(ma: MemAddr, dp: Lset DirPermission) returns (value: Value)
{
  assert dp == WholeDirPermission(ma);
  call value := atomic_read_mem#0(ma);
}
yield procedure {:layer 1} read_mem(ma: MemAddr, {:layer 1} dp: Lset DirPermission) returns (value: Value)
refines atomic_read_mem;
{
  call value := read_mem#0(ma);
}

atomic action {:layer 1,2} atomic_read_mem#0(ma: MemAddr) returns (value: Value)
{
  value := mem[ma];
}
yield procedure {:layer 0} read_mem#0(ma: MemAddr) returns (value: Value);
refines atomic_read_mem#0;

atomic action {:layer 2} atomic_write_mem(ma: MemAddr, value: Value, dp: Lset DirPermission)
modifies mem;
{
  assert dp == WholeDirPermission(ma);
  call atomic_write_mem#0(ma, value);
}
yield procedure {:layer 1} write_mem(ma: MemAddr, value: Value, {:layer 1} dp: Lset DirPermission)
refines atomic_write_mem;
{
  call write_mem#0(ma, value);
}

atomic action {:layer 1,2} atomic_write_mem#0(ma: MemAddr, value: Value)
modifies mem;
{
  mem[ma] := value;
}
yield procedure {:layer 0} write_mem#0(ma: MemAddr, value: Value);
refines atomic_write_mem#0;
