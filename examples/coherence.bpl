// RUN: %parallel-boogie "%s" > "%t"

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


// Atomic actions for channels and memory
atomic action {:layer 1,2} atomic_read_back(i: CacheId, ma: MemAddr) returns (ticket: int)
{
  ticket := back[i][ma];
}
yield procedure {:layer 0} read_back(i: CacheId, ma: MemAddr) returns (ticket: int);
refines atomic_read_back;

atomic action {:layer 1,2} atomic_increment_back(i: CacheId, ma: MemAddr) returns (ticket: int)
modifies back;
{
  ticket := back[i][ma];
  back[i][ma] := back[i][ma] + 1;
}
yield procedure {:layer 0} increment_back(i: CacheId, ma: MemAddr) returns (ticket: int);
refines atomic_increment_back;

atomic action {:layer 1,2} atomic_increment_front(i: CacheId, ma: MemAddr)
modifies front;
{
  front[i][ma] := front[i][ma] + 1;
}
yield procedure {:layer 0} increment_front(i: CacheId, ma: MemAddr);
refines atomic_increment_front;

atomic action {:layer 1,2} atomic_read_mem(ma: MemAddr) returns (value: Value)
{
  value := mem[ma];
}
yield procedure {:layer 0} read_mem(ma: MemAddr) returns (value: Value);
refines atomic_read_mem;

atomic action {:layer 1,2} atomic_write_mem(ma: MemAddr, value: Value)
modifies mem;
{
  mem[ma] := value;
}
yield procedure {:layer 0} write_mem(ma: MemAddr, value: Value);
refines atomic_write_mem;


// Permission actions
action {:layer 1,2} GetDirRequestPermissionAtCache(i: CacheId, ma: MemAddr, cond: bool) returns (drp: Lset DirRequestPermission)
modifies dirRequestPermissionsAtCache;
{
  var p: [DirRequestPermission]bool;
  if (cond) {
    p := MapOne(DirRequestPermission(i, ma));
    drp := Lset(p);
    call Lset_Split(drp, dirRequestPermissionsAtCache);
  } else {
    call drp := Lset_Empty();
  }
}

action {:layer 1,2} PutDirRequestPermissionAtCache({:linear_in} drp: Lset DirRequestPermission)
modifies dirRequestPermissionsAtCache;
{
  call Lset_Transfer(drp, dirRequestPermissionsAtCache);
}

action {:layer 1,2} GetDirRequestPermissionAtDir(i: CacheId, ma: MemAddr, cond: bool) returns (drp: Lset DirRequestPermission)
modifies dirRequestPermissionsAtDir;
{
  var p: [DirRequestPermission]bool;
  if (cond) {
    p := MapOne(DirRequestPermission(i, ma));
    drp := Lset(p);
    call Lset_Split(drp, dirRequestPermissionsAtDir);
  } else {
    call drp := Lset_Empty();
  }
}

action {:layer 1,2} PutDirRequestPermissionAtDir({:linear_in} drp: Lset DirRequestPermission)
modifies dirRequestPermissionsAtDir;
{
  call Lset_Transfer(drp, dirRequestPermissionsAtDir);
}

action {:layer 1,2} EmptyDirRequestPermission() returns (drp: Lset DirRequestPermission)
{
  call drp := Lset_Empty();
}

action {:layer 1,2} GetDirPermission(ma: MemAddr) returns (dp: Lval DirPermission)
modifies dirPermissions;
{
  var p: DirPermission;
  p := DirPermission(ma);
  dp := Lval(p);
  call Lval_Split(dp, dirPermissions);
}

action {:layer 1,2} PutDirPermission(ma: MemAddr, {:linear_in} dp: Lval DirPermission)
modifies dirPermissions;
{
  call Lval_Transfer(dp, dirPermissions);
}

action {:layer 1} GetSnoopPermission(i: CacheId, ma: MemAddr) returns (sp: Lval SnoopPermission)
modifies snoopPermissions;
{
  var p: SnoopPermission;
  p := SnoopPermission(i, ma, back[i][ma]);
  sp := Lval(p);
  call Lval_Split(sp, snoopPermissions);
}

action {:layer 1} PutSnoopPermission(i: CacheId, ma: MemAddr, {:linear_in} sp: Lval SnoopPermission)
modifies snoopPermissions;
{
  call Lval_Transfer(sp, snoopPermissions);
}


// at cache
yield procedure {:layer 2} cache_read_share_req(i: CacheId, ma: MemAddr) returns (result: Option Value)
{
  var line: CacheLine;
  var {:layer 1,2} drp: Lset DirRequestPermission;
  call result, line, drp := cache_req_begin(i, ReadShared(ma));
  if (result is Some) {
    return;
  }
  if (!(line->currRequest is NoCacheRequest)) {
    return;
  }
  if (line->state == Invalid()) {
    async call dir_read_share_req(i, ma, drp);
  } else if (line->state == Modified()) {
    async call dir_evict_req(i, ma, Some(line->value), drp);
  } else {
    async call dir_evict_req(i, ma, None(), drp);
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
  if (!(line->currRequest is NoCacheRequest)) {
    return;
  }
  if (line->state == Invalid() || line->ma == ma) {
    async call dir_read_own_req(i, ma, drp);
  } else if (line->state == Modified()) {
    async call dir_evict_req(i, ma, Some(line->value), drp);
  } else {
    async call dir_evict_req(i, ma, None(), drp);
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
  if (!(line->currRequest is NoCacheRequest)) {
    return;
  }
  if (line->state == Invalid() || line->ma == ma) {
    async call dir_read_own_req(i, ma, drp);
  } else if (line->state == Modified()) {
    async call dir_evict_req(i, ma, Some(line->value), drp);
  } else {
    async call dir_evict_req(i, ma, None(), drp);
  }
}

atomic action {:layer 2} atomic_cache_req_begin(i: CacheId, currRequest: CacheRequest) returns (result: Option Value, line: CacheLine, drp: Lset DirRequestPermission)
modifies cache, dirRequestPermissionsAtCache;
{
  call result, line := atomic_cache_req_begin#0(i, currRequest);
  call drp := GetDirRequestPermissionAtCache(i, currRequest->ma, result is None && line->currRequest is NoCacheRequest);
}
yield procedure {:layer 1} cache_req_begin(i: CacheId, currRequest: CacheRequest) returns (result: Option Value, line: CacheLine, {:layer 1} drp: Lset DirRequestPermission)
refines atomic_cache_req_begin;
{
  call result, line := cache_req_begin#0(i, currRequest);
  call drp := GetDirRequestPermissionAtCache(i, currRequest->ma, result is None && line->currRequest is NoCacheRequest);
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

yield procedure {:layer 2} cache_read_resp(i: CacheId, ma: MemAddr, v: Value, s: State, ticket: int, {:linear_in} {:layer 1} drp: Lset DirRequestPermission)
{
  call cache_read_resp(i, ma, v, s, ticket, drp);
}

atomic action {:layer 2} atomic_cache_read_resp#1(i: CacheId, ma: MemAddr, v: Value, s: State, ticket: int, {:linear_in} drp: Lset DirRequestPermission)
modifies cache, front, dirRequestPermissionsAtCache, dirRequestPermissionsAtDir;
{
  call atomic_cache_read_resp#0(i, ma, v, s, ticket);
  call PutDirRequestPermissionAtCache(drp);
}
yield procedure {:layer 1} cache_read_resp#1(i: CacheId, ma: MemAddr, v: Value, s: State, ticket: int, {:linear_in} {:layer 1} drp: Lset DirRequestPermission)
refines atomic_cache_read_resp#1;
{
  call cache_read_resp#0(i, ma, v, s, ticket);
  call PutDirRequestPermissionAtCache(drp);
}

atomic action {:layer 1,2} atomic_cache_read_resp#0(i: CacheId, ma: MemAddr, v: Value, s: State, ticket: int)
modifies cache, front;
{
  var currRequest: CacheRequest;
  var ca: CacheAddr;
  assume ticket == front[i][ma];
  front[i][ma] := front[i][ma] + 1;
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
yield procedure {:layer 0} cache_read_resp#0(i: CacheId, ma: MemAddr, v: Value, s: State, ticket: int);
refines atomic_cache_read_resp#0;

yield procedure {:layer 2} cache_evict_resp(i: CacheId, ma: MemAddr, ticket: int, {:linear_in} {:layer 1,2} drp: Lset DirRequestPermission)
{
  var currRequest: CacheRequest;
  call currRequest := cache_evict_resp_begin(i, ma, ticket);
  if (currRequest is ReadShared) {
    async call dir_read_share_req(i, currRequest->ma, drp);
  } else {
    async call dir_read_own_req(i, currRequest->ma, drp);
  }
}

atomic action {:layer 1,2} atomic_cache_evict_resp_begin(i: CacheId, ma: MemAddr, ticket: int) returns (currRequest: CacheRequest)
modifies cache, front;
{
  var line: CacheLine;
  var ca: CacheAddr;
  assume ticket == front[i][ma];
  front[i][ma] := front[i][ma] + 1;
  ca := Hash(ma);
  line := cache[i][ca];
  assert line->ma == ma;
  assert !(line->currRequest is NoCacheRequest);
  cache[i][ca]->state := Invalid();
}
yield procedure {:layer 0} cache_evict_resp_begin(i: CacheId, ma: MemAddr, ticket: int) returns (currRequest: CacheRequest);
refines atomic_cache_evict_resp_begin;

yield procedure {:layer 2} cache_snoop_req(i: CacheId, ma: MemAddr, s: State, ticket: int)
{
  var opt_value: Option Value;
  call opt_value := cache_snoop_req_begin(i, ma, s, ticket);
  async call dir_snoop_resp(i, ma, opt_value);
}

atomic action {:layer 1,2} atomic_cache_snoop_req_begin(i: CacheId, ma: MemAddr, s: State, ticket: int) returns (opt_value: Option Value)
modifies cache;
{
  var ca: CacheAddr;
  var line: CacheLine;
  assume ticket == front[i][ma];
  ca := Hash(ma);
  line := cache[i][ca];
  assert s == Invalid() || s == Shared();
  assert line->state != Invalid() && line->state != s;
  assert line->ma == ma;
  if (line->state == Modified()) {
    opt_value := Some(line->value);
  } else {
    opt_value := None();
  }
  cache[i][ca]->state := s;
}
yield procedure {:layer 0} cache_snoop_req_begin(i: CacheId, ma: MemAddr, s: State, ticket: int) returns (opt_value: Option Value);
refines atomic_cache_snoop_req_begin;


// at dir
yield procedure {:layer 2} dir_read_share_req(i: CacheId, ma: MemAddr, {:linear_in} {:layer 1,2} drp: Lset DirRequestPermission)
{
  var dirInfo: DirInfo;
  var dirState: DirState;
  var {:layer 1,2} drp': Lset DirRequestPermission;
  var {:layer 1,2} dp: Lval DirPermission;
  call dirInfo, drp', dp := dir_req_begin(ma, Share(i), drp);
  dirState := dirInfo->state;
  if (dirState is Owner) {
    call dir_snoop_victims(ma, Set_Singleton(dirState->i), Shared());
  } else {
    call dirState := dir_read_req_middle(i, ma, dirState, drp');
  }
}

yield procedure {:layer 2} dir_read_own_req(i: CacheId, ma: MemAddr, {:linear_in} {:layer 1,2} drp: Lset DirRequestPermission)
{
  var dirInfo: DirInfo;
  var dirState: DirState;
  var {:layer 1,2} drp': Lset DirRequestPermission;
  var {:layer 1,2} dp: Lval DirPermission;
  call dirInfo, drp', dp := dir_req_begin(ma, Own(i), drp);
  dirState := dirInfo->state;
  if (dirState is Owner) {
    call dir_snoop_victims(ma, Set_Singleton(dirState->i), Invalid());
  } else if (dirState == Sharers(Set_Empty())) {
    call dirState := dir_read_req_middle(i, ma, dirState, drp');
  } else {
    call dir_snoop_victims(ma, dirState->iset, Invalid());
  }
}

yield procedure {:layer 2} dir_evict_req(i: CacheId, ma: MemAddr, opt_value: Option Value, {:linear_in} {:layer 1,2} drp: Lset DirRequestPermission)
{
  var dirInfo: DirInfo;
  var dirState: DirState;
  var {:layer 1,2} drp': Lset DirRequestPermission;
  var {:layer 1,2} dp: Lval DirPermission;
  call dirInfo, drp', dp := dir_req_begin(ma, Evict(i), drp);
  if (opt_value is Some) {
    call write_mem(ma, opt_value->t);
  }
  dirState := dirInfo->state;
  call dirState := dir_evict_req_middle(i, ma, dirState, drp');
}

yield procedure {:layer 2} dir_snoop_resp(i: CacheId, ma: MemAddr, opt_value: Option Value)
{
  var dirInfo: DirInfo;
  var {:layer 1} drp: Lset DirRequestPermission;
  var dirState: DirState;
  var currRequest: DirRequest;
  call dirInfo, drp := dir_snoop_resp_begin(i, ma); // get dirPermission
  if (opt_value is Some) {
    call write_mem(ma, opt_value->t);
  }
  dirState := dirInfo->state;
  currRequest := dirInfo->currRequest;
  call dirState := dir_snoop_resp_middle(ma, dirInfo, drp);
}

atomic action {:layer 2} atomic_dir_req_begin(ma: MemAddr, dirRequest: DirRequest, {:linear_in} drp: Lset DirRequestPermission)
returns (dirInfo: DirInfo, drp': Lset DirRequestPermission, dp: Lval DirPermission)
modifies back, dir, dirRequestPermissionsAtDir, dirPermissions;
{
  var dirState: DirState;
  call dirInfo := atomic_dir_req_begin#0(ma, dirRequest);
  dirState := dirInfo->state;
  drp' := drp;
  if ((dirRequest is Share && dirState is Owner) || (dirRequest is Own && dirState != Sharers(Set_Empty()))) {
    call PutDirRequestPermissionAtDir(drp');
    call drp' := EmptyDirRequestPermission();
  }
  call dp := GetDirPermission(ma);
}
yield procedure {:layer 1} dir_req_begin(ma: MemAddr, dirRequest: DirRequest, {:linear_in} {:layer 1} drp: Lset DirRequestPermission)
returns (dirInfo: DirInfo, {:layer 1} drp': Lset DirRequestPermission, {:layer 1} dp: Lval DirPermission)
refines atomic_dir_req_begin;
{
  var dirState: DirState;
  call dirInfo := dir_req_begin#0(ma, dirRequest);
  dirState := dirInfo->state;
  drp' := drp;
  if ((dirRequest is Share && dirState is Owner) || (dirRequest is Own && dirState != Sharers(Set_Empty()))) {
    call PutDirRequestPermissionAtDir(drp');
    call drp' := EmptyDirRequestPermission();
  }
  call dp := GetDirPermission(ma);
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

yield procedure {:layer 2} dir_snoop_victims(ma: MemAddr, _victims: Set CacheId, state: State)
{
  var victims: Set CacheId;
  var victim: CacheId;
  var ticket: int;
  victims := _victims;
  while (victims != Set_Empty()) {
    victim := Set_Choose(victims);
    victims := Set_Remove(victims, victim);
    call ticket := read_back(victim, ma);
    async call cache_snoop_req(victim, ma, state, ticket);
  }
}

yield procedure {:layer 2} dir_read_req_middle(i: CacheId, ma: MemAddr, dirState: DirState, {:linear_in} {:layer 1} drp: Lset DirRequestPermission) returns (dirState': DirState)
{
  var ticket: int;
  var value: Value;
  call value := read_mem(ma);
  call ticket := increment_back(i, ma);
  if (dirState->iset == Set_Empty()) {
    dirState' := Owner(i);
    async call cache_read_resp(i, ma, value, Exclusive(), ticket, drp);
  } else {
    dirState' := Sharers(Set_Add(dirState->iset, i));
    async call cache_read_resp(i, ma, value, Shared(), ticket, drp);
  }
  call dir_req_end(ma, dirState');
}

yield procedure {:layer 2} dir_evict_req_middle(i: CacheId, ma: MemAddr, dirState: DirState, {:linear_in} {:layer 1,2} drp: Lset DirRequestPermission) returns (dirState': DirState)
{
  var ticket: int;
  call ticket := increment_back(i, ma);
  async call cache_evict_resp(i, ma, ticket, drp);
  if (dirState is Owner) {
    dirState' := Sharers(Set_Empty());
  } else {
    dirState' := Sharers(Set_Remove(dirState->iset, i));
  }
  call dir_req_end(ma, dirState');
}

atomic action {:layer 2} atomic_dir_snoop_resp_begin(i: CacheId, ma: MemAddr) returns (dirInfo: DirInfo, {:layer 1} drp: Lset DirRequestPermission)
modifies dir, dirRequestPermissionsAtDir;
{
  call dirInfo := atomic_dir_snoop_resp_begin#0(i, ma);
  call drp := GetDirRequestPermissionAtDir(i, ma, dirInfo->state is Owner || dirInfo->state == Sharers(Set_Empty()));
}
yield procedure {:layer 1} dir_snoop_resp_begin(i: CacheId, ma: MemAddr) returns (dirInfo: DirInfo, {:layer 1} drp: Lset DirRequestPermission)
refines atomic_dir_snoop_resp_begin;
{
  call dirInfo := dir_snoop_resp_begin#0(i, ma);
  call drp := GetDirRequestPermissionAtDir(i, ma, dirInfo->state is Owner || dirInfo->state == Sharers(Set_Empty()));
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

yield procedure {:layer 2} dir_snoop_resp_middle(ma: MemAddr, dirInfo: DirInfo, {:linear_in} {:layer 1} drp: Lset DirRequestPermission) returns (dirState: DirState)
{
  var currRequest: DirRequest;
  var ticket: int;
  var value: Value;
  dirState := dirInfo->state;
  currRequest := dirInfo->currRequest;
  if (dirState is Owner || dirState == Sharers(Set_Empty())) {
    call value := read_mem(ma);
    call ticket := increment_back(currRequest->i, ma);
    if (currRequest is Own) {
      async call cache_read_resp(currRequest->i, ma, value, Exclusive(), ticket, drp);
      dirState := Owner(dirInfo->currRequest->i);
    } else {
      async call cache_read_resp(currRequest->i, ma, value, Shared(), ticket, drp);
      dirState := Sharers(Set_Add(Set_Singleton(dirState->i), currRequest->i));
    }
    call dir_req_end(ma, dirState);
  }
}

atomic action {:layer 1,2} atomic_dir_req_end(ma: MemAddr, dirState: DirState)
modifies dir;
{
  assert !(dir[ma]->currRequest is NoDirRequest);
  dir[ma]->state := dirState;
  dir[ma]->currRequest := NoDirRequest();
}
yield procedure {:layer 0} dir_req_end(ma: MemAddr, dirState: DirState);
refines atomic_dir_req_end;
