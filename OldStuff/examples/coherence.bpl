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
  EvictCache(ma: MemAddr),
  ReadShared(ma: MemAddr),
  ReadOwn(ma: MemAddr),
  NoCacheRequest()
}

datatype Result {
  Ok(),
  Fail()
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

function {:inline} WholeDirPermission(ma: MemAddr): Set DirPermission {
  Set((lambda {:pool "DirPermission"} x: DirPermission :: x->ma == ma))
}

datatype SnoopPermission {
  SnoopPermission(i: CacheId, ma: MemAddr, ticket: int)
}

var {:layer 0,3} mem: [MemAddr]Value;
var {:layer 0,3} dir: [MemAddr]DirInfo;
var {:layer 0,3} cache: [CacheId]Cache;

var {:layer 0,3} front: [CacheId][MemAddr]int;
var {:layer 0,3} back: [CacheId][MemAddr]int;

var {:layer 1,3} dirRequestPermissionsAtCache: Set DirRequestPermission;
var {:layer 1,3} dirRequestPermissionsAtDir: Set DirRequestPermission;
var {:layer 1,3} snoopPermissions: Set SnoopPermission;
var {:layer 1,3} dirPermissions: Set DirPermission;


// at cache
atomic action {:layer 1,2} atomic_cache_read(i: CacheId, ma: MemAddr) returns (result: Option Value)
modifies cache;
{
  var ca: CacheAddr;
  var line: CacheLine;
  ca := Hash(ma);
  line := cache[i][ca];
  result := None();
  if (line->state != Invalid() && line->ma == ma) {
    result := Some(line->value);
  }
}
yield procedure {:layer 0} cache_read(i: CacheId, ma: MemAddr) returns (result: Option Value);
refines atomic_cache_read;

atomic action {:layer 1,2} atomic_cache_write(i: CacheId, ma: MemAddr, v: Value) returns (result: Result)
modifies cache;
{
  var ca: CacheAddr;
  var line: CacheLine;
  ca := Hash(ma);
  line := cache[i][ca];
  result := Fail();
  if (line->state != Invalid() && line->state != Shared() && line->ma == ma) {
    cache[i][ca]->value := v;
    cache[i][ca]->state := Modified();
    result := Ok();
  }
}
yield procedure {:layer 0} cache_write(i: CacheId, ma: MemAddr, v: Value) returns (result: Result);
refines atomic_cache_write;

yield procedure {:layer 2} cache_evict_req(i: CacheId, ca: CacheAddr) returns (result: Result)
{
  var line: CacheLine;
  var {:layer 1,2} drp: Set DirRequestPermission;
  call result, line, drp := cache_evict_req#1(i, ca);
  if (line->state != Invalid()) {
    if (line->currRequest == NoCacheRequest()) {
      async call dir_evict_req(i, line->ma, if line->state is Modified then Some(line->value) else None(), drp);
    }
  }
}

atomic action {:layer 2} atomic_cache_evict_req#1(i: CacheId, ca: CacheAddr)
returns (result: Result, line: CacheLine, drp: Set DirRequestPermission)
modifies cache, dirRequestPermissionsAtCache;
{
  call result, line := atomic_cache_evict_req#0(i, ca);
  call drp := Set_MakeEmpty();
  if (line->state != Invalid()) {
    if (line->currRequest == NoCacheRequest()) {
      call drp := Set_Get(dirRequestPermissionsAtCache, MapOne(DirRequestPermission(i, ca)));
    }
  }
}
yield procedure {:layer 1} cache_evict_req#1(i: CacheId, ca: CacheAddr)
returns (result: Result, line: CacheLine, {:layer 1} drp: Set DirRequestPermission)
refines atomic_cache_evict_req#1;
{
  call result, line := cache_evict_req#0(i, ca);
  call {:layer 1} drp := Set_MakeEmpty();
  if (line->state != Invalid()) {
    if (line->currRequest == NoCacheRequest()) {
      call {:layer 1} drp := Set_Get(dirRequestPermissionsAtCache, MapOne(DirRequestPermission(i, ca)));
    }
  }
}

atomic action {:layer 1,2} atomic_cache_evict_req#0(i: CacheId, ca: CacheAddr) returns (result: Result, line: CacheLine)
modifies cache;
{
  line := cache[i][ca];
  if (line->state != Invalid()) {
    call result := acquire_cache_lock(i, ca, EvictCache(line->ma));
  } else {
    result := Ok();
  }
}
yield procedure {:layer 0} cache_evict_req#0(i: CacheId, ca: CacheAddr) returns (result: Result, line: CacheLine);
refines atomic_cache_evict_req#0;

yield procedure {:layer 2} cache_read_share_req(i: CacheId, ma: MemAddr) returns (result: Result)
{
  var line: CacheLine;
  var {:layer 1,2} drp: Set DirRequestPermission;
  call result, line, drp := cache_read_share_req#1(i, ma);
  if (line->state == Invalid()) {
    if (line->currRequest == NoCacheRequest()) {
      async call dir_read_share_req(i, ma, drp);
    }
  }
}

atomic action {:layer 2} atomic_cache_read_share_req#1(i: CacheId, ma: MemAddr)
returns (result: Result, line: CacheLine, drp: Set DirRequestPermission)
modifies cache, dirRequestPermissionsAtCache;
{
  call result, line := atomic_cache_read_share_req#0(i, ma);
  call drp := Set_MakeEmpty();
  if (line->state == Invalid()) {
    if (line->currRequest == NoCacheRequest()) {
      call drp := Set_Get(dirRequestPermissionsAtCache, MapOne(DirRequestPermission(i, Hash(ma))));
    }
  }
}
yield procedure {:layer 1} cache_read_share_req#1(i: CacheId, ma: MemAddr)
returns (result: Result, line: CacheLine, {:layer 1} drp: Set DirRequestPermission)
refines atomic_cache_read_share_req#1;
{
  call result, line := cache_read_share_req#0(i, ma);
  call {:layer 1} drp := Set_MakeEmpty();
  if (line->state == Invalid()) {
    if (line->currRequest == NoCacheRequest()) {
      call {:layer 1} drp := Set_Get(dirRequestPermissionsAtCache, MapOne(DirRequestPermission(i, Hash(ma))));
    }
  }
}

atomic action {:layer 1,2} atomic_cache_read_share_req#0(i: CacheId, ma: MemAddr) returns (result: Result, line: CacheLine)
modifies cache;
{
  var ca: CacheAddr;
  ca := Hash(ma);
  line := cache[i][ca];
  if (line->state == Invalid()) {
    call result := acquire_cache_lock(i, ca, ReadShared(ma));
  } else {
    result := if line->ma == ma then Ok() else Fail();
  }
}
yield procedure {:layer 0} cache_read_share_req#0(i: CacheId, ma: MemAddr) returns (result: Result, line: CacheLine);
refines atomic_cache_read_share_req#0;

yield procedure {:layer 2} cache_read_own_req(i: CacheId, ma: MemAddr) returns (result: Result)
{
  var line: CacheLine;
  var {:layer 1,2} drp: Set DirRequestPermission;
  call result, line, drp := cache_read_own_req#1(i, ma);
  if (line->state == Invalid() || (line->ma == ma && line->state == Shared())) {
    if (line->currRequest == NoCacheRequest()) {
      async call dir_read_own_req(i, ma, drp);
    }
  }
}

atomic action {:layer 2} atomic_cache_read_own_req#1(i: CacheId, ma: MemAddr)
returns (result: Result, line: CacheLine, drp: Set DirRequestPermission)
modifies cache, dirRequestPermissionsAtCache;
{
  call result, line := atomic_cache_read_own_req#0(i, ma);
  call drp := Set_MakeEmpty();
  if (line->state == Invalid() || (line->ma == ma && line->state == Shared())) {
    if (line->currRequest == NoCacheRequest()) {
      call drp := Set_Get(dirRequestPermissionsAtCache, MapOne(DirRequestPermission(i, Hash(ma))));
    }
  }
}
yield procedure {:layer 1} cache_read_own_req#1(i: CacheId, ma: MemAddr)
returns (result: Result, line: CacheLine, {:layer 1} drp: Set DirRequestPermission)
refines atomic_cache_read_own_req#1;
{
  call result, line := cache_read_own_req#0(i, ma);
  call {:layer 1} drp := Set_MakeEmpty();
  if (line->state == Invalid() || (line->ma == ma && line->state == Shared())) {
    if (line->currRequest == NoCacheRequest()) {
      call {:layer 1} drp := Set_Get(dirRequestPermissionsAtCache, MapOne(DirRequestPermission(i, Hash(ma))));
    }
  }
}

atomic action {:layer 1,2} atomic_cache_read_own_req#0(i: CacheId, ma: MemAddr) returns (result: Result, line: CacheLine)
modifies cache;
{
  var ca: CacheAddr;
  ca := Hash(ma);
  line := cache[i][ca];
  if (line->state == Invalid() || (line->ma == ma && line->state == Shared())) {
    call result := acquire_cache_lock(i, ca, ReadOwn(ma));
  } else {
    result := if line->ma == ma then Ok() else Fail();
  }
}
yield procedure {:layer 0} cache_read_own_req#0(i: CacheId, ma: MemAddr) returns (result: Result, line: CacheLine);
refines atomic_cache_read_own_req#0;

action {:layer 1,2} acquire_cache_lock(i: CacheId, ca: CacheAddr, currRequest: CacheRequest) returns (result: Result)
modifies cache;
{
  if (cache[i][ca]->currRequest is NoCacheRequest) {
    cache[i][ca]->currRequest := currRequest;
    result := Ok();
  } else {
    result := Fail();
  }
}

async atomic action {:layer 3} atomic_cache_read_resp(i: CacheId, ma: MemAddr, v: Value, s: State, ticket: int, {:linear_in} drp: Set DirRequestPermission, {:linear_in} sp: One SnoopPermission)
modifies cache, front, dirRequestPermissionsAtCache;
{
  assert Set_Contains(drp, DirRequestPermission(i, Hash(ma)));
  assert sp == One(SnoopPermission(i, ma, ticket));
  assert ticket >= front[i][ma];
  assume ticket == front[i][ma];
  call primitive_cache_read_resp_begin(i, ma, v, s);
  front[i][ma] := front[i][ma] + 1;
  call Set_Put(dirRequestPermissionsAtCache, drp);
}
yield procedure {:layer 2} cache_read_resp(i: CacheId, ma: MemAddr, v: Value, s: State, ticket: int, {:layer 1,2} {:linear_in} drp: Set DirRequestPermission, {:layer 1,2} {:linear_in} sp: One SnoopPermission)
refines atomic_cache_read_resp;
{
  call wait_front(i, ma, ticket);
  call cache_read_resp_begin(i, ma, v, s, drp);
  call increment_front(i, ma);
}

atomic action {:layer 2} atomic_cache_read_resp_begin(i: CacheId, ma: MemAddr, v: Value, s: State, {:linear_in} drp: Set DirRequestPermission)
modifies cache, front, dirRequestPermissionsAtCache;
{
  call primitive_cache_read_resp_begin(i, ma, v, s);
  call Set_Put(dirRequestPermissionsAtCache, drp);
}
yield procedure {:layer 1} cache_read_resp_begin(i: CacheId, ma: MemAddr, v: Value, s: State, {:layer 1} {:linear_in} drp: Set DirRequestPermission)
refines atomic_cache_read_resp_begin;
{
  call cache_read_resp_begin#0(i, ma, v, s);
  call {:layer 1} Set_Put(dirRequestPermissionsAtCache, drp);
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
  var line: CacheLine;
  ca := Hash(ma);
  line := cache[i][ca];
  currRequest := line->currRequest;
  assert currRequest->ma == ma;
  assert line->state == Invalid() || (line->state == Shared() && line->ma == ma);
  if (currRequest is ReadShared) {
    assert s == Shared();
  } else if (currRequest is ReadOwn) {
    assert s == Exclusive();
  } else {
    assert false;
  }
  cache[i][ca] := CacheLine(ma, v, s, NoCacheRequest());
}

async atomic action {:layer 3} atomic_cache_evict_resp(i: CacheId, ma: MemAddr, ticket: int, {:linear_in} drp: Set DirRequestPermission, {:linear_in} sp: One SnoopPermission)
modifies cache, front, dirRequestPermissionsAtCache;
creates atomic_dir_read_share_req, atomic_dir_read_own_req;
{
  var currRequest: CacheRequest;
  var asyncCallReadShareReq: atomic_dir_read_share_req;
  var asyncCallReadOwnReq: atomic_dir_read_own_req;
  assert Set_Contains(drp, DirRequestPermission(i, Hash(ma)));
  assert sp == One(SnoopPermission(i, ma, ticket));
  assert ticket >= front[i][ma];
  assume ticket == front[i][ma];
  call currRequest := primitive_cache_evict_resp_begin(i, ma);
  front[i][ma] := front[i][ma] + 1;
  if (currRequest is EvictCache) {
    call Set_Put(dirRequestPermissionsAtCache, drp);
  } else if (currRequest is ReadShared) {
    asyncCallReadShareReq := atomic_dir_read_share_req(i, currRequest->ma, drp);
    call create_async(asyncCallReadShareReq);
  } else {
    asyncCallReadOwnReq := atomic_dir_read_own_req(i, currRequest->ma, drp);
    call create_async(asyncCallReadOwnReq);
  }
}
yield procedure {:layer 2} cache_evict_resp(i: CacheId, ma: MemAddr, ticket: int, {:layer 1,2} {:linear_in} drp: Set DirRequestPermission, {:layer 1,2} {:linear_in} sp: One SnoopPermission)
refines atomic_cache_evict_resp;
{
  var currRequest: CacheRequest;
  var {:layer 1,2} drp': Set DirRequestPermission;
  call wait_front(i, ma, ticket);
  call currRequest, drp' := cache_evict_resp_begin(i, ma, drp);
  call increment_front(i, ma);
  if (currRequest is EvictCache) {
    // do nothing
  } else if (currRequest is ReadShared) {
    async call dir_read_share_req(i, currRequest->ma, drp');
  } else {
    async call dir_read_own_req(i, currRequest->ma, drp');
  }
}

atomic action {:layer 2} atomic_cache_evict_resp_begin(i: CacheId, ma: MemAddr, {:linear_in} drp: Set DirRequestPermission) 
returns (currRequest: CacheRequest, drp': Set DirRequestPermission)
modifies cache, dirRequestPermissionsAtCache;
{
  drp' := drp;
  call currRequest := primitive_cache_evict_resp_begin(i, ma);
  if (currRequest is EvictCache) {
    call Set_Put(dirRequestPermissionsAtCache, drp');
    call drp' := Set_MakeEmpty();
  }
}
yield procedure {:layer 1} cache_evict_resp_begin(i: CacheId, ma: MemAddr, {:layer 1} {:linear_in} drp: Set DirRequestPermission)
returns (currRequest: CacheRequest, {:layer 1} drp': Set DirRequestPermission)
refines atomic_cache_evict_resp_begin;
{
  drp' := drp;
  call currRequest := cache_evict_resp_begin#0(i, ma);
  if (currRequest is EvictCache) {
    call {:layer 1} Set_Put(dirRequestPermissionsAtCache, drp');
    call {:layer 1} drp' := Set_MakeEmpty();
  }
}

atomic action {:layer 1} atomic_cache_evict_resp_begin#0(i: CacheId, ma: MemAddr) returns (currRequest: CacheRequest)
modifies cache;
{
  call currRequest := primitive_cache_evict_resp_begin(i, ma);
}
yield procedure {:layer 0} cache_evict_resp_begin#0(i: CacheId, ma: MemAddr) returns (currRequest: CacheRequest);
refines atomic_cache_evict_resp_begin#0;

action {:layer 1,3} primitive_cache_evict_resp_begin(i: CacheId, ma: MemAddr) returns (currRequest: CacheRequest)
modifies cache;
{
  var line: CacheLine;
  var ca: CacheAddr;
  ca := Hash(ma);
  line := cache[i][ca];
  assert line->ma == ma;
  assert !(line->currRequest is NoCacheRequest);
  currRequest := line->currRequest;
  cache[i][ca]->state := Invalid();
  if (currRequest is EvictCache) {
    line->currRequest := NoCacheRequest();
  }
}

async atomic action {:layer 3} atomic_cache_snoop_exclusive_req(i: CacheId, ma: MemAddr, s: State, ticket: int, {:linear_in} dp: Set DirPermission, {:linear_in} sp: One SnoopPermission)
modifies cache;
creates atomic_dir_snoop_exclusive_resp;
{
  var opt_value: Option Value;
  var asyncCall: atomic_dir_snoop_exclusive_resp;
  assert sp == One(SnoopPermission(i, ma, ticket));
  assert ticket >= front[i][ma];
  assume ticket == front[i][ma];
  call opt_value := primitive_cache_snoop_exclusive_req_begin(i, ma, s);
  asyncCall := atomic_dir_snoop_exclusive_resp(i, ma, opt_value, dp, sp);
  call create_async(asyncCall);
}
yield procedure {:layer 2} cache_snoop_exclusive_req(i: CacheId, ma: MemAddr, s: State, ticket: int, {:layer 1,2} {:linear_in} dp: Set DirPermission, {:layer 1,2} {:linear_in} sp: One SnoopPermission)
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

async atomic action {:layer 3} atomic_cache_snoop_shared_req(i: CacheId, ma: MemAddr, ticket: int, {:linear_in} dpOne: Set DirPermission, {:linear_in} sp: One SnoopPermission)
modifies cache;
creates atomic_dir_snoop_shared_resp;
{
  var asyncCall: atomic_dir_snoop_shared_resp;
  assert sp == One(SnoopPermission(i, ma, ticket));
  assert ticket >= front[i][ma];
  assume ticket == front[i][ma];
  call primitive_cache_snoop_shared_req_begin(i, ma);
  asyncCall := atomic_dir_snoop_shared_resp(i, ma, dpOne, sp);
  call create_async(asyncCall);
}
yield procedure {:layer 2} cache_snoop_shared_req(i: CacheId, ma: MemAddr, ticket: int, {:layer 1,2} {:linear_in} dpOne: Set DirPermission, {:layer 1,2} {:linear_in} sp: One SnoopPermission)
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
async atomic action {:layer 3} atomic_dir_read_share_req(i: CacheId, ma: MemAddr, {:linear_in} drp: Set DirRequestPermission)
modifies dir, back, dirPermissions, snoopPermissions, dirRequestPermissionsAtDir;
creates atomic_cache_snoop_exclusive_req, atomic_cache_read_resp;
{
  var dirState: DirState;
  var ticket: int;
  var dp: Set DirPermission;
  var sp: One SnoopPermission;
  var asyncCallCacheSnoopExclusive: atomic_cache_snoop_exclusive_req;
  var asyncCallCacheRead: atomic_cache_read_resp;
  assume dir[ma]->currRequest == NoDirRequest();
  assert Set_IsSubset(WholeDirPermission(ma), dirPermissions);
  dirState := dir[ma]->state;
  if (dirState is Owner) {
    dir[ma]->currRequest := Share(i);
    ticket := back[dirState->i][ma];
    call Set_Put(dirRequestPermissionsAtDir, drp);
    call dp := Set_Get(dirPermissions, WholeDirPermission(ma)->dom);
    call sp := One_Get(snoopPermissions, SnoopPermission(dirState->i, ma, ticket));
    asyncCallCacheSnoopExclusive := atomic_cache_snoop_exclusive_req(dirState->i, ma, Shared(), ticket, dp, sp);
    call create_async(asyncCallCacheSnoopExclusive);
  } else {
    ticket := back[i][ma];
    back[i][ma] := back[i][ma] + 1;
    dir[ma]->state := if dirState->iset == Set_Empty() then Owner(i) else Sharers(Set_Add(dirState->iset, i));
    call sp := One_Get(snoopPermissions, SnoopPermission(i, ma, ticket));
    asyncCallCacheRead := atomic_cache_read_resp(i, ma, mem[ma], if dirState->iset == Set_Empty() then Exclusive() else Shared(), ticket, drp, sp);
    call create_async(asyncCallCacheRead);
  }
}
yield procedure {:layer 2} dir_read_share_req(i: CacheId, ma: MemAddr, {:layer 1,2} {:linear_in} drp: Set DirRequestPermission)
refines atomic_dir_read_share_req;
{
  var dirInfo: DirInfo;
  var dirState: DirState;
  var ticket: int;
  var value: Value;
  var {:layer 1,2} drp': Set DirRequestPermission;
  var {:layer 1,2} dp: Set DirPermission;
  var {:layer 1,2} sp: One SnoopPermission;
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

async atomic action {:layer 3} atomic_dir_read_own_req(i: CacheId, ma: MemAddr, {:linear_in} drp: Set DirRequestPermission)
modifies dir, back, dirPermissions, snoopPermissions, dirRequestPermissionsAtDir;
creates atomic_cache_snoop_exclusive_req, atomic_cache_snoop_shared_req, atomic_cache_read_resp;
{
  var dirState: DirState;
  var ticket: int;
  var dp: Set DirPermission;
  var sp: One SnoopPermission;
  var sps: Set SnoopPermission;
  var asyncCallCacheSnoopExclusive: atomic_cache_snoop_exclusive_req;
  var asyncCallCacheRead: atomic_cache_read_resp;
  assume dir[ma]->currRequest == NoDirRequest();
  assert Set_IsSubset(WholeDirPermission(ma), dirPermissions);
  dirState := dir[ma]->state;
  if (dirState is Owner) {
    dir[ma]->currRequest := Own(i);
    ticket := back[dirState->i][ma];
    call Set_Put(dirRequestPermissionsAtDir, drp);
    call dp := Set_Get(dirPermissions, WholeDirPermission(ma)->dom);
    call sp := One_Get(snoopPermissions, SnoopPermission(dirState->i, ma, ticket));
    asyncCallCacheSnoopExclusive := atomic_cache_snoop_exclusive_req(dirState->i, ma, Invalid(), ticket, dp, sp);
    call create_async(asyncCallCacheSnoopExclusive);
  } else if (dirState == Sharers(Set_Empty())) {
    ticket := back[i][ma];
    back[i][ma] := back[i][ma] + 1;
    dir[ma]->state := if dirState->iset == Set_Empty() then Owner(i) else Sharers(Set_Add(dirState->iset, i));
    call sp := One_Get(snoopPermissions, SnoopPermission(i, ma, ticket));
    asyncCallCacheRead := atomic_cache_read_resp(i, ma, mem[ma], if dirState->iset == Set_Empty() then Exclusive() else Shared(), ticket, drp, sp);
    call create_async(asyncCallCacheRead);
  } else {
    dir[ma]->currRequest := Own(i);
    call Set_Put(dirRequestPermissionsAtDir, drp);
    call dp := Set_Get(dirPermissions, (lambda x: DirPermission :: x->ma == ma && Set_Contains(dirState->iset, x->i)));
    call sps := Set_Get(snoopPermissions, (lambda x: SnoopPermission :: 
      Set_Contains(dirState->iset, x->i) && 
      x->ma == ma && 
      x->ticket == back[x->i][x->ma]));
    call create_asyncs((lambda x: atomic_cache_snoop_shared_req :: 
      Set_Contains(dirState->iset, x->i) && 
      x->ma == ma && 
      x->ticket == back[x->i][x->ma] && 
      x->dpOne == Set(MapOne(DirPermission(x->i, x->ma))) && 
      x->sp == One(SnoopPermission(x->i, x->ma, x->ticket))));
  }
}
yield procedure {:layer 2} dir_read_own_req(i: CacheId, ma: MemAddr, {:layer 1,2} {:linear_in} drp: Set DirRequestPermission)
refines atomic_dir_read_own_req;
{
  var dirInfo: DirInfo;
  var dirState: DirState;
  var ticket: int;
  var value: Value;
  var {:layer 1,2} drp': Set DirRequestPermission;
  var {:layer 1,2} dp: Set DirPermission;
  var {:layer 1,2} sp: One SnoopPermission;
  var {:layer 1,2} dpOne: Set DirPermission;
  var victims: Set CacheId;
  var victim: CacheId;
  var {:layer 2} oldSnoopPermissions: [SnoopPermission]bool;
  var {:layer 2} {:pending_async} PAs:[atomic_cache_snoop_shared_req]int;

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
    call {:layer 2} oldSnoopPermissions := Copy(snoopPermissions->dom);
    while (victims != Set_Empty())
    invariant {:yields} {:layer 1} true;
    invariant {:layer 2} dp == Set((lambda x: DirPermission :: Set_Contains(victims, x->i) && x->ma == ma));
    invariant {:layer 2} Set_IsSubset(victims, dirState->iset);
    invariant {:layer 2} snoopPermissions->dom == MapDiff(oldSnoopPermissions,
      (lambda x: SnoopPermission :: Set_Contains(Set_Difference(dirState->iset, victims), x->i) && x->ma == ma && x->ticket == back[x->i][x->ma]));
    invariant {:layer 2} IsSubset(
      (lambda x: SnoopPermission :: Set_Contains(victims, x->i) && x->ma == ma && x->ticket == back[x->i][x->ma]), snoopPermissions->dom);
    invariant {:layer 2} PAs == ToMultiset(
      (lambda x: atomic_cache_snoop_shared_req :: 
        Set_Contains(Set_Difference(dirState->iset, victims), x->i) && 
        x->ma == ma && 
        x->ticket == back[x->i][x->ma] &&
        x->dpOne == Set(MapOne(DirPermission(x->i, x->ma))) && 
        x->sp == One(SnoopPermission(x->i, x->ma, x->ticket))));
    {
      call victim, dpOne, dp := get_victim(ma, victims, dp);
      victims := Set_Remove(victims, victim);
      call ticket, sp := read_back(victim, ma, dpOne);
      async call cache_snoop_shared_req(victim, ma, ticket, dpOne, sp);
    }
  }
}

both action {:layer 2} atomic_get_victim(ma: MemAddr, victims: Set CacheId, {:layer 1} {:linear_in} dp: Set DirPermission) 
returns (victim: CacheId, {:layer 1} dpOne: Set DirPermission, {:layer 1} dp': Set DirPermission)
{
  victim := Choice(victims->val);
  dp' := dp;
  call dpOne := Set_Get(dp', MapOne(DirPermission(victim, ma)));
}
yield procedure {:layer 1} get_victim(ma: MemAddr, victims: Set CacheId, {:layer 1} {:linear_in} dp: Set DirPermission) 
returns (victim: CacheId, {:layer 1} dpOne: Set DirPermission, {:layer 1} dp': Set DirPermission) 
refines atomic_get_victim;
{
  victim := Choice(victims->val);
  dp' := dp;
  call {:layer 1} dpOne := Set_Get(dp', MapOne(DirPermission(victim, ma)));
}

async atomic action {:layer 3} atomic_dir_evict_req(i: CacheId, ma: MemAddr, opt_value: Option Value, {:linear_in} drp: Set DirRequestPermission)
modifies mem, back, dir, snoopPermissions;
creates atomic_cache_evict_resp;
{
  var ticket: int;
  var sp: One SnoopPermission;
  var asyncCall: atomic_cache_evict_resp;
  assume dir[ma]->currRequest == NoDirRequest();
  if (opt_value is Some) {
    mem[ma] := opt_value->t;
  }
  assert Set_IsSubset(WholeDirPermission(ma), dirPermissions);
  ticket := back[i][ma];
  back[i][ma] := back[i][ma] + 1;
  dir[ma]->state := if dir[ma]->state is Owner then Sharers(Set_Empty()) else Sharers(Set_Remove(dir[ma]->state->iset, i));
  call sp := One_Get(snoopPermissions, SnoopPermission(i, ma, ticket));
  asyncCall := atomic_cache_evict_resp(i, ma, ticket, drp, sp);
  call create_async(asyncCall);
}
yield procedure {:layer 2} dir_evict_req(i: CacheId, ma: MemAddr, opt_value: Option Value, {:layer 1,2} {:linear_in} drp: Set DirRequestPermission)
refines atomic_dir_evict_req;
{
  var dirInfo: DirInfo;
  var dirState: DirState;
  var ticket: int;
  var {:layer 1,2} drp': Set DirRequestPermission;
  var {:layer 1,2} dp: Set DirPermission;
  var {:layer 1,2} sp: One SnoopPermission;
  call dirInfo, drp', dp := dir_req_begin(ma, Evict(i), drp);
  if (opt_value is Some) {
    call write_mem(ma, opt_value->t, dp);
  }
  dirState := dirInfo->state;
  call ticket, sp := increment_back(i, ma, dp);
  call dir_req_end(ma, if dirState is Owner then Sharers(Set_Empty()) else Sharers(Set_Remove(dirState->iset, i)), dp);
  async call cache_evict_resp(i, ma, ticket, drp', sp);
}

right action {:layer 2} atomic_dir_req_begin(ma: MemAddr, dirRequest: DirRequest, {:linear_in} drp: Set DirRequestPermission)
returns (dirInfo: DirInfo, drp': Set DirRequestPermission, dp: Set DirPermission)
modifies back, dir, dirRequestPermissionsAtDir, dirPermissions;
{
  var dirState: DirState;
  assume {:add_to_pool "DirPermission", DirPermission(i0, ma)} true;
  call dirInfo := primitive_dir_req_begin(ma, dirRequest);
  call drp', dp, dirPermissions, dirRequestPermissionsAtDir := 
    dir_req_move_permissions(ma, dirRequest, dirInfo->state, drp, dirPermissions, dirRequestPermissionsAtDir);
}
yield procedure {:layer 1} dir_req_begin(ma: MemAddr, dirRequest: DirRequest, {:layer 1} {:linear_in} drp: Set DirRequestPermission)
returns (dirInfo: DirInfo, {:layer 1} drp': Set DirRequestPermission, {:layer 1} dp: Set DirPermission)
refines atomic_dir_req_begin;
{
  call dirInfo := dir_req_begin#0(ma, dirRequest);
  call {:layer 1} drp', dp, dirPermissions, dirRequestPermissionsAtDir := 
    dir_req_move_permissions(ma, dirRequest, dirInfo->state, drp, dirPermissions, dirRequestPermissionsAtDir);
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

left action {:layer 2} atomic_dir_req_end(ma: MemAddr, dirState: DirState, {:linear_in} dp: Set DirPermission)
modifies dir, dirPermissions;
{
  assert dp == WholeDirPermission(ma);
  assume {:add_to_pool "DirPermission", DirPermission(i0, ma)} true;
  call primitive_dir_req_end(ma, dirState);
  call Set_Put(dirPermissions, dp);
}
yield procedure {:layer 1} dir_req_end(ma: MemAddr, dirState: DirState, {:layer 1} {:linear_in} dp: Set DirPermission)
refines atomic_dir_req_end;
{
  call dir_req_end#0(ma, dirState);
  call {:layer 1} Set_Put(dirPermissions, dp);
}

pure action dir_req_move_permissions(
  ma: MemAddr, 
  dirRequest: DirRequest, 
  dirState: DirState, 
  {:linear_in} drp: Set DirRequestPermission,
  {:linear_in} dirPermissions: Set DirPermission,
  {:linear_in} dirRequestPermissionsAtDir: Set DirRequestPermission) 
  returns (
    drp': Set DirRequestPermission,
    dp: Set DirPermission,
    dirPermissions': Set DirPermission,
    dirRequestPermissionsAtDir': Set DirRequestPermission)
{
  drp', dirPermissions', dirRequestPermissionsAtDir' := drp, dirPermissions, dirRequestPermissionsAtDir;
  if ((dirRequest is Share && dirState is Owner) || (dirRequest is Own && dirState != Sharers(Set_Empty()))) {
    call Set_Put(dirRequestPermissionsAtDir', drp');
    call drp' := Set_MakeEmpty();
  }
  if (dirRequest is Own && dirState is Sharers && dirState->iset != Set_Empty()) {
    assume {:add_to_pool "DirPermission", DirPermission(Choice(dirState->iset->val), ma)} true;
    call dp := Set_Get(dirPermissions', (lambda x: DirPermission :: x->ma == ma && Set_Contains(dirState->iset, x->i)));
  } else {
    call dp := Set_Get(dirPermissions', WholeDirPermission(ma)->dom);
  }
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

async atomic action {:layer 3} atomic_dir_snoop_exclusive_resp(i: CacheId, ma: MemAddr, opt_value: Option Value, {:linear_in} dp: Set DirPermission, {:linear_in} sp: One SnoopPermission)
modifies mem, dir, back, dirPermissions, snoopPermissions, dirRequestPermissionsAtDir;
creates atomic_cache_read_resp;
{
  var dirInfo: DirInfo;
  var dirState: DirState;
  var currRequest: DirRequest;
  var ticket: int;
  var value: Value;
  var drp': Set DirRequestPermission;
  var sp': One SnoopPermission;
  var asyncCall: atomic_cache_read_resp;
  assert dp == WholeDirPermission(ma);
  if (opt_value is Some) {
    mem[ma] := opt_value->t;
  }
  dirInfo := dir[ma];
  dirState := dirInfo->state;
  assert dirState is Owner;
  assert dirState->i == i;
  currRequest := dirInfo->currRequest;
  assert !(currRequest is NoDirRequest);
  call Set_Put(dirPermissions, dp);
  call One_Put(snoopPermissions, sp);
  value := mem[ma];
  ticket := back[currRequest->i][ma];
  back[currRequest->i][ma] := ticket + 1;
  call drp' := Set_Get(dirRequestPermissionsAtDir, MapOne(DirRequestPermission(currRequest->i, Hash(ma))));
  call sp' := One_Get(snoopPermissions, SnoopPermission(currRequest->i, ma, ticket));
  dir[ma]->state  := if currRequest is Own then Owner(currRequest->i) else Sharers(Set_Add(Set_Singleton(dirState->i), currRequest->i));
  dir[ma]->currRequest := NoDirRequest();
  asyncCall := atomic_cache_read_resp(currRequest->i, ma, value, if currRequest is Own then Exclusive() else Shared(), ticket, drp', sp');
  call create_async(asyncCall);
}
yield procedure {:layer 2} dir_snoop_exclusive_resp(i: CacheId, ma: MemAddr, opt_value: Option Value, {:layer 1,2} {:linear_in} dp: Set DirPermission, {:layer 1,2} {:linear_in} sp: One SnoopPermission)
refines atomic_dir_snoop_exclusive_resp;
{
  var dirInfo: DirInfo;
  var dirState: DirState;
  var currRequest: DirRequest;
  var value: Value;
  var ticket: int;
  var {:layer 1,2} drp: Set DirRequestPermission;
  var {:layer 1,2} sp': One SnoopPermission;
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

async atomic action {:layer 3} atomic_dir_snoop_shared_resp(i: CacheId, ma: MemAddr, {:linear_in} dpOne: Set DirPermission, {:linear_in} sp: One SnoopPermission)
modifies dir, back, dirPermissions, snoopPermissions, dirRequestPermissionsAtDir;
creates atomic_cache_read_resp;
{
  var dirState: DirState;
  var currRequest: DirRequest;
  var ticket: int;
  var value: Value;
  var drp': Set DirRequestPermission;
  var sp': One SnoopPermission;
  var asyncCall: atomic_cache_read_resp;
  
  assert Set_Contains(dpOne, DirPermission(i, ma));
  DirInfo(dirState, currRequest) := dir[ma];
  assert dirState is Sharers && Set_Contains(dirState->iset, i);
  assert currRequest is Own;
  call Set_Put(dirPermissions, dpOne);
  call One_Put(snoopPermissions, sp);
  dirState := Sharers(Set_Remove(dirState->iset, i));
  if (dirState != Sharers(Set_Empty())) {
    dir[ma]->state := dirState;
    return;
  }
  assert Set_IsSubset(WholeDirPermission(ma), dirPermissions);
  value := mem[ma];
  ticket := back[currRequest->i][ma];
  back[currRequest->i][ma] := ticket + 1;
  call drp' := Set_Get(dirRequestPermissionsAtDir, MapOne(DirRequestPermission(currRequest->i, Hash(ma))));
  call sp' := One_Get(snoopPermissions, SnoopPermission(currRequest->i, ma, ticket));
  dir[ma] := DirInfo(Owner(currRequest->i), NoDirRequest());
  asyncCall := atomic_cache_read_resp(currRequest->i, ma, value, Exclusive(), ticket, drp', sp');
  call create_async(asyncCall);
}
yield procedure {:layer 2} dir_snoop_shared_resp(i: CacheId, ma: MemAddr, {:layer 1,2} {:linear_in} dpOne: Set DirPermission, {:layer 1,2} {:linear_in} sp: One SnoopPermission)
refines atomic_dir_snoop_shared_resp;
{
  var dirInfo: DirInfo;
  var dirState: DirState;
  var currRequest: DirRequest;
  var value: Value;
  var ticket: int;
  var {:layer 1,2} drp: Set DirRequestPermission;
  var {:layer 1,2} {:linear} dp: Set DirPermission;
  var {:layer 1,2} sp': One SnoopPermission;
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

atomic action {:layer 2} atomic_dir_snoop_exclusive_resp_begin(i: CacheId, ma: MemAddr, dp: Set DirPermission, {:linear_in} sp: One SnoopPermission) returns (dirInfo: DirInfo, drp: Set DirRequestPermission)
modifies dir, dirRequestPermissionsAtDir, snoopPermissions;
{
  assert dp == WholeDirPermission(ma);
  assume {:add_to_pool "DirPermission", DirPermission(i0, ma)} true;
  call dirInfo := primitive_dir_snoop_resp_begin(i, ma);
  call drp, dirRequestPermissionsAtDir, snoopPermissions := 
    dir_snoop_exclusive_resp_move_permissions(ma, dirInfo, sp, dirRequestPermissionsAtDir, snoopPermissions);
}
yield procedure {:layer 1} dir_snoop_exclusive_resp_begin(i: CacheId, ma: MemAddr, {:layer 1} dp: Set DirPermission, {:layer 1} {:linear_in} sp: One SnoopPermission) returns (dirInfo: DirInfo, {:layer 1} drp: Set DirRequestPermission)
refines atomic_dir_snoop_exclusive_resp_begin;
{
  call dirInfo := dir_snoop_resp_begin#0(i, ma);
  call {:layer 1} drp, dirRequestPermissionsAtDir, snoopPermissions := 
    dir_snoop_exclusive_resp_move_permissions(ma, dirInfo, sp, dirRequestPermissionsAtDir, snoopPermissions);
}

pure action dir_snoop_exclusive_resp_move_permissions(
  ma: MemAddr,
  dirInfo: DirInfo,
  {:linear_in} sp: One SnoopPermission,
  {:linear_in} dirRequestPermissionsAtDir: Set DirRequestPermission,
  {:linear_in} snoopPermissions: Set SnoopPermission)
  returns (
    drp: Set DirRequestPermission,
    dirRequestPermissionsAtDir': Set DirRequestPermission,
    snoopPermissions': Set SnoopPermission)
{
  dirRequestPermissionsAtDir', snoopPermissions' := dirRequestPermissionsAtDir, snoopPermissions;
  call One_Put(snoopPermissions', sp);
  call drp := Set_Get(dirRequestPermissionsAtDir', MapOne(DirRequestPermission(dirInfo->currRequest->i, Hash(ma))));
}

atomic action {:layer 2} atomic_dir_snoop_shared_resp_begin(i: CacheId, ma: MemAddr, {:linear_in} dpOne: Set DirPermission, {:linear_in} sp: One SnoopPermission)
returns (dirInfo: DirInfo, drp: Set DirRequestPermission, dp: Set DirPermission)
modifies dir, dirRequestPermissionsAtDir, dirPermissions, snoopPermissions;
{
  assert Set_Contains(dpOne, DirPermission(i, ma));
  call dirInfo := primitive_dir_snoop_resp_begin(i, ma);
  call drp, dp, dirPermissions, dirRequestPermissionsAtDir, snoopPermissions := 
    dir_snoop_shared_resp_move_permissions(ma, dirInfo, dpOne, sp, dirPermissions, dirRequestPermissionsAtDir, snoopPermissions);
}
yield procedure {:layer 1} dir_snoop_shared_resp_begin(i: CacheId, ma: MemAddr, {:layer 1} {:linear_in} dpOne: Set DirPermission, {:layer 1} {:linear_in} sp: One SnoopPermission)
returns (dirInfo: DirInfo, {:layer 1} drp: Set DirRequestPermission, {:layer 1} dp: Set DirPermission)
refines atomic_dir_snoop_shared_resp_begin;
{
  call dirInfo := dir_snoop_resp_begin#0(i, ma);
  call {:layer 1} drp, dp, dirPermissions, dirRequestPermissionsAtDir, snoopPermissions := 
    dir_snoop_shared_resp_move_permissions(ma, dirInfo, dpOne, sp, dirPermissions, dirRequestPermissionsAtDir, snoopPermissions);
}

pure action dir_snoop_shared_resp_move_permissions(
  ma: MemAddr,
  dirInfo: DirInfo,
  {:linear_in} dpOne: Set DirPermission, 
  {:linear_in} sp: One SnoopPermission, 
  {:linear_in} dirPermissions: Set DirPermission,
  {:linear_in} dirRequestPermissionsAtDir: Set DirRequestPermission,
  {:linear_in} snoopPermissions: Set SnoopPermission)
  returns (
    drp: Set DirRequestPermission, 
    dp: Set DirPermission, 
    dirPermissions': Set DirPermission, 
    dirRequestPermissionsAtDir': Set DirRequestPermission, 
    snoopPermissions': Set SnoopPermission)
{
  dirPermissions', dirRequestPermissionsAtDir', snoopPermissions' := dirPermissions, dirRequestPermissionsAtDir, snoopPermissions;
  call Set_Put(dirPermissions', dpOne);
  call One_Put(snoopPermissions', sp);
  if (dirInfo->state == Sharers(Set_Empty())) {
    call drp := Set_Get(dirRequestPermissionsAtDir', MapOne(DirRequestPermission(dirInfo->currRequest->i, Hash(ma))));
    call dp := Set_Get(dirPermissions', WholeDirPermission(ma)->dom);
  } else {
    call drp := Set_MakeEmpty();
    call dp := Set_MakeEmpty();
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


// Atomic actions for channels and memory
both action {:layer 2} atomic_read_back(i: CacheId, ma: MemAddr, dp: Set DirPermission) returns (ticket: int, sp: One SnoopPermission)
modifies snoopPermissions;
{
  assert Set_Contains(dp, DirPermission(i, ma));
  ticket := back[i][ma];
  call sp := One_Get(snoopPermissions, SnoopPermission(i, ma, ticket));
}
yield procedure {:layer 1} read_back(i: CacheId, ma: MemAddr, {:layer 1} dp: Set DirPermission) returns (ticket: int, {:layer 1} sp: One SnoopPermission)
refines atomic_read_back;
{
  call ticket := read_back#0(i, ma);
  call {:layer 1} sp := One_Get(snoopPermissions, SnoopPermission(i, ma, ticket));
}

atomic action {:layer 1} atomic_read_back#0(i: CacheId, ma: MemAddr) returns (ticket: int)
{
  ticket := back[i][ma];
}
yield procedure {:layer 0} read_back#0(i: CacheId, ma: MemAddr) returns (ticket: int);
refines atomic_read_back#0;

both action {:layer 2} atomic_increment_back(i: CacheId, ma: MemAddr, dp: Set DirPermission) returns (ticket: int, sp: One SnoopPermission)
modifies back, snoopPermissions;
{
  assert dp == WholeDirPermission(ma);
  assume {:add_to_pool "DirPermission", DirPermission(i0, ma)} true;
  ticket := back[i][ma];
  back[i][ma] := back[i][ma] + 1;
  call sp := One_Get(snoopPermissions, SnoopPermission(i, ma, ticket));
}
yield procedure {:layer 1} increment_back(i: CacheId, ma: MemAddr, {:layer 1} dp: Set DirPermission) returns (ticket: int, {:layer 1} sp: One SnoopPermission)
refines atomic_increment_back;
{
  call ticket := increment_back#0(i, ma);
  call {:layer 1} sp := One_Get(snoopPermissions, SnoopPermission(i, ma, ticket));
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
refines atomic_wait_front#0;

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

both action {:layer 2} atomic_read_mem(ma: MemAddr, dp: Set DirPermission) returns (value: Value)
{
  assert dp == WholeDirPermission(ma);
  assume {:add_to_pool "DirPermission", DirPermission(i0, ma)} true;
  value := mem[ma];
}
yield procedure {:layer 1} read_mem(ma: MemAddr, {:layer 1} dp: Set DirPermission) returns (value: Value)
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

both action {:layer 2} atomic_write_mem(ma: MemAddr, value: Value, dp: Set DirPermission)
modifies mem;
{
  assert dp == WholeDirPermission(ma);
  assume {:add_to_pool "DirPermission", DirPermission(i0, ma)} true;
  mem[ma] := value;
}
yield procedure {:layer 1} write_mem(ma: MemAddr, value: Value, {:layer 1} dp: Set DirPermission)
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
