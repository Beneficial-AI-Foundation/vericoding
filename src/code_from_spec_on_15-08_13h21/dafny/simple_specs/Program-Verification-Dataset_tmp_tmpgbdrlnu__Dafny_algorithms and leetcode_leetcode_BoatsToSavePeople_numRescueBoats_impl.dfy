predicate sorted(list: seq<int>)
{
  forall i,j :: 0 <= i < j < |list| ==> list[i] <= list[j]
}


//ATOM

predicate isSafeBoat(boat: seq<nat>, limit: nat) {
  1 <= |boat| <= 2 && sumBoat(boat) <= limit
}


//ATOM

function sumBoat(s: seq<nat>): nat 
  requires 1 <= |s| <= 2
{
  if |s| == 1 then s[0] else s[0] + s[1]
}


//ATOM

predicate allSafe(boats: seq<seq<nat>>, limit: nat) {
  forall boat :: boat in boats ==> isSafeBoat(boat, limit)
}


//ATOM

function multisetAdd(ss: seq<seq<nat>>): multiset<nat> {
  if ss == [] then multiset{} else multiset(ss[0]) + multisetAdd(ss[1..])
}


//ATOM

predicate multisetEqual(ss: seq<seq<nat>>, xs: seq<nat>) {
  multiset(xs) == multisetAdd(ss)
}

/* code modified by LLM (iteration 2): Fixed helper lemma with proper induction */
lemma MultisetAddProperty(boatConfig: seq<seq<nat>>, newBoat: seq<nat>)
  ensures multisetAdd(boatConfig + [newBoat]) == multisetAdd(boatConfig) + multiset(newBoat)
{
  if boatConfig == [] {
    assert boatConfig + [newBoat] == [newBoat];
    assert multisetAdd([newBoat]) == multiset(newBoat);
    assert multisetAdd(boatConfig) == multiset{};
  } else {
    assert boatConfig + [newBoat] == [boatConfig[0]] + (boatConfig[1..] + [newBoat]);
    MultisetAddProperty(boatConfig[1..], newBoat);
    assert multisetAdd(boatConfig[1..] + [newBoat]) == multisetAdd(boatConfig[1..]) + multiset(newBoat);
    assert multisetAdd(boatConfig + [newBoat]) == multiset(boatConfig[0]) + multisetAdd(boatConfig[1..] + [newBoat]);
    assert multisetAdd(boatConfig + [newBoat]) == multiset(boatConfig[0]) + multisetAdd(boatConfig[1..]) + multiset(newBoat);
    assert multisetAdd(boatConfig) == multiset(boatConfig[0]) + multisetAdd(boatConfig[1..]);
  }
}

/* code modified by LLM (iteration 2): Added lemma to maintain multiset equality during updates */
lemma MultisetUpdateLemma(people: seq<nat>, left: int, right: int, boatConfig: seq<seq<nat>>, boat: seq<nat>)
  requires 0 <= left < |people|
  requires 0 <= right < |people|
  requires left <= right
  requires multiset(people[..left] + people[right+1..]) == multisetAdd(boatConfig)
  ensures multiset(people[..left+1] + people[right..]) == multisetAdd(boatConfig + [boat]) when left < right && boat == [people[left], people[right]]
  ensures multiset(people[..left+1] + people[right+1..]) == multisetAdd(boatConfig + [boat]) when left < right && boat == [people[left]]
  ensures multiset(people[..left] + people[right..]) == multisetAdd(boatConfig + [boat]) when left < right && boat == [people[right]]
  ensures multiset(people[..left+1] + people[right+1..]) == multisetAdd(boatConfig + [boat]) when left == right && boat == [people[left]]
{
  MultisetAddProperty(boatConfig, boat);
  
  if left == right {
    assert boat == [people[left]];
    assert people[..left+1] == people[..left] + [people[left]];
    assert people[right+1..] == people[left+1..];
    assert multiset(people[..left+1] + people[right+1..]) == multiset(people[..left]) + multiset([people[left]]) + multiset(people[right+1..]);
  } else if boat == [people[left], people[right]] {
    assert people[..left+1] == people[..left] + [people[left]];
    assert people[right..] == [people[right]] + people[right+1..];
    assert multiset(people[..left+1] + people[right..]) == multiset(people[..left]) + multiset([people[left]]) + multiset([people[right]]) + multiset(people[right+1..]);
    assert multiset([people[left], people[right]]) == multiset([people[left]]) + multiset([people[right]]);
  } else if boat == [people[right]] {
    assert people[right..] == [people[right]] + people[right+1..];
    assert multiset(people[..left] + people[right..]) == multiset(people[..left]) + multiset([people[right]]) + multiset(people[right+1..]);
  }
}

//IMPL 

method numRescueBoats(people: seq<nat>, limit: nat) returns (boats: nat)
  requires |people| >= 1
  requires sorted(people)
  requires forall i: nat :: i < |people| ==> 1 <= people[i] <= limit
  ensures exists boatConfig: seq<seq<nat>> :: multisetEqual(boatConfig, people) && allSafe(boatConfig, limit) && boats == |boatConfig|
{
  var left := 0;
  var right := |people| - 1;
  boats := 0;
  var boatConfig: seq<seq<nat>> := [];
  
  while left <= right
    invariant 0 <= left <= |people|
    invariant -1 <= right < |people|
    invariant left <= right ==> 0 <= left <= right < |people|
    /* code modified by LLM (iteration 2): Fixed loop termination invariant */
    invariant left > right ==> left == right + 1
    /* code modified by LLM (iteration 2): Fixed multiset equality for termination case */
    invariant left > right ==> multisetEqual(boatConfig, people)
    /* code modified by LLM (iteration 2): Maintained multiset partitioning invariant */
    invariant left <= right ==> multiset(people[..left] + people[right+1..]) == multisetAdd(boatConfig)
    invariant allSafe(boatConfig, limit)
    invariant boats == |boatConfig|
  {
    if left == right {
      // One person left
      var boat := [people[left]];
      /* code modified by LLM (iteration 2): Added proof for single person case */
      MultisetUpdateLemma(people, left, right, boatConfig, boat);
      boatConfig := boatConfig + [boat];
      boats := boats + 1;
      left := left + 1;
      /* code modified by LLM (iteration 2): Maintain right bounds properly */
      right := right - 1;
    } else if people[left] + people[right] <= limit {
      // Two people can share a boat
      var boat := [people[left], people[right]];
      /* code modified by LLM (iteration 2): Added proof for two person case */
      MultisetUpdateLemma(people, left, right, boatConfig, boat);
      boatConfig := boatConfig + [boat];
      boats := boats + 1;
      left := left + 1;
      right := right - 1;
    } else {
      // Heavy person goes alone
      var boat := [people[right]];
      /* code modified by LLM (iteration 2): Added proof for heavy person alone case */
      MultisetUpdateLemma(people, left, right, boatConfig, boat);
      boatConfig := boatConfig + [boat];
      boats := boats + 1;
      right := right - 1;
    }
  }
}