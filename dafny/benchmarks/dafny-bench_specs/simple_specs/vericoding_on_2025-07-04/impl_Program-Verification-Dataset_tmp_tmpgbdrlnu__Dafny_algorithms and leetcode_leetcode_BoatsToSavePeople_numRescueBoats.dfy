//ATOM

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


//IMPL

/* code modified by LLM (iteration 1): Added comprehensive helper lemmas for multiset properties */
lemma multisetAddAppend(ss1: seq<seq<nat>>, ss2: seq<seq<nat>>)
  ensures multisetAdd(ss1 + ss2) == multisetAdd(ss1) + multisetAdd(ss2)
{
  if ss1 == [] {
    assert ss1 + ss2 == ss2;
    assert multisetAdd(ss1) == multiset{};
  } else {
    multisetAddAppend(ss1[1..], ss2);
    assert ss1 + ss2 == [ss1[0]] + (ss1[1..] + ss2);
  }
}

lemma multisetAddSingle(boat: seq<nat>)
  ensures multisetAdd([boat]) == multiset(boat)
{
  assert multisetAdd([boat]) == multiset(boat) + multisetAdd([]);
  assert multisetAdd([]) == multiset{};
}

/* code modified by LLM (iteration 1): Added helper lemma for sequence slicing */
lemma sequenceSliceProperty(people: seq<nat>, left: int, right: int)
  requires 0 <= left <= right < |people|
  ensures people[left..right+1] == people[left..left+1] + people[left+1..right+1]
  ensures multiset(people[left..right+1]) == multiset(people[left..left+1]) + multiset(people[left+1..right+1])
{
}

/* code modified by LLM (iteration 1): Added helper lemma for two-element slices */
lemma twoElementSlice(people: seq<nat>, left: int, right: int)
  requires 0 <= left < right < |people|
  ensures people[left..right+1] == [people[left]] + people[left+1..right] + [people[right]]
  ensures multiset(people[left..right+1]) == multiset([people[left]]) + multiset(people[left+1..right]) + multiset([people[right]])
{
  if left + 1 == right {
    assert people[left..right+1] == [people[left], people[right]];
    assert people[left+1..right] == [];
  } else {
    sequenceSliceProperty(people, left, right);
    sequenceSliceProperty(people, left+1, right);
  }
}

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
  
  /* code modified by LLM (iteration 1): Simplified loop invariants */
  while left <= right
    invariant 0 <= left <= |people|
    invariant -1 <= right < |people|
    invariant left > right ==> multisetAdd(boatConfig) == multiset(people)
    invariant left <= right ==> multisetAdd(boatConfig) + multiset(people[left..right+1]) == multiset(people)
    invariant allSafe(boatConfig, limit)
    invariant boats == |boatConfig|
    decreases right - left + 1
  {
    if left == right {
      /* code modified by LLM (iteration 1): Single person case */
      var boat := [people[left]];
      
      assert sumBoat(boat) == people[left] <= limit;
      assert isSafeBoat(boat, limit);
      
      multisetAddSingle(boat);
      multisetAddAppend(boatConfig, [boat]);
      assert people[left..right+1] == [people[left]];
      assert multiset(people[left..right+1]) == multiset([people[left]]);
      
      boatConfig := boatConfig + [boat];
      boats := boats + 1;
      left := left + 1;
      
    } else if people[left] + people[right] <= limit {
      /* code modified by LLM (iteration 1): Two person case */
      var boat := [people[left], people[right]];
      
      assert sumBoat(boat) == people[left] + people[right] <= limit;
      assert isSafeBoat(boat, limit);
      
      multisetAddSingle(boat);
      multisetAddAppend(boatConfig, [boat]);
      twoElementSlice(people, left, right);
      assert multiset(boat) == multiset([people[left]]) + multiset([people[right]]);
      
      boatConfig := boatConfig + [boat];
      boats := boats + 1;
      left := left + 1;
      right := right - 1;
      
    } else {
      /* code modified by LLM (iteration 1): Heavy person alone case */
      var boat := [people[right]];
      
      assert sumBoat(boat) == people[right] <= limit;
      assert isSafeBoat(boat, limit);
      
      multisetAddSingle(boat);
      multisetAddAppend(boatConfig, [boat]);
      sequenceSliceProperty(people, left, right);
      assert people[right..right+1] == [people[right]];
      assert multiset(boat) == multiset([people[right]]);
      
      boatConfig := boatConfig + [boat];
      boats := boats + 1;
      right := right - 1;
    }
  }
}