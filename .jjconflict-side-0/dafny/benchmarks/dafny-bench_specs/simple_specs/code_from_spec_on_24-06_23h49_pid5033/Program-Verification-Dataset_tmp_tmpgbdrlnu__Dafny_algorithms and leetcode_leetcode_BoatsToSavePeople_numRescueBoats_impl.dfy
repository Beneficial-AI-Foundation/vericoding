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


/* code modified by LLM (iteration 1): Added comprehensive helper lemmas with proper proofs */
lemma multisetAddAppend(s1: seq<seq<nat>>, s2: seq<seq<nat>>)
  ensures multisetAdd(s1 + s2) == multisetAdd(s1) + multisetAdd(s2)
{
  if s1 == [] {
    assert s1 + s2 == s2;
    assert multisetAdd(s1) == multiset{};
  } else {
    assert s1 + s2 == [s1[0]] + (s1[1..] + s2);
    multisetAddAppend(s1[1..], s2);
  }
}

lemma multisetAddSingle(boat: seq<nat>)
  ensures multisetAdd([boat]) == multiset(boat)
{
  assert multisetAdd([boat]) == multiset(boat) + multisetAdd([]);
  assert multisetAdd([]) == multiset{};
}

lemma multisetSequenceDecomposition(people: seq<nat>, left: nat, right: nat)
  requires 0 <= left <= right < |people|
  ensures multiset(people) == multiset(people[..left]) + multiset(people[left..right+1]) + multiset(people[right+1..])
{
  assert people == people[..left] + people[left..right+1] + people[right+1..];
}

lemma multisetRangeDecomposition(people: seq<nat>, left: nat, right: nat)
  requires 0 <= left < right < |people|
  ensures multiset(people[left..right+1]) == multiset{people[left]} + multiset(people[left+1..right]) + multiset{people[right]}
{
  assert people[left..right+1] == [people[left]] + people[left+1..right] + [people[right]];
}

lemma multisetSingleRange(people: seq<nat>, idx: nat)
  requires 0 <= idx < |people|
  ensures multiset(people[idx..idx+1]) == multiset{people[idx]}
{
  assert people[idx..idx+1] == [people[idx]];
}

/* code modified by LLM (iteration 1): Added helper lemma for range update reasoning */
lemma multisetRangeUpdate(people: seq<nat>, left: nat, right: nat, boat: seq<nat>)
  requires 0 <= left <= right < |people|
  requires left < right ==> boat == [people[left], people[right]]
  requires left == right ==> boat == [people[left]]
  ensures left < right ==> multiset(people[left..right+1]) == multiset(boat) + multiset(people[left+1..right])
  ensures left == right ==> multiset(people[left..right+1]) == multiset(boat)
{
  if left < right {
    multisetRangeDecomposition(people, left, right);
    assert multiset{people[left]} + multiset{people[right]} == multiset([people[left], people[right]]);
  } else {
    multisetSingleRange(people, left);
  }
}

//IMPL numRescueBoats

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
  
  /* code modified by LLM (iteration 1): Added initialization lemma call */
  multisetSequenceDecomposition(people, left, right);
  
  /* code modified by LLM (iteration 1): Improved loop invariants with proper bounds and multiset reasoning */
  while left <= right
    invariant 0 <= left <= |people|
    invariant 0 <= right < |people|
    invariant left > right ==> multisetAdd(boatConfig) == multiset(people)
    invariant left <= right ==> multisetAdd(boatConfig) + multiset(people[left..right+1]) == multiset(people)
    invariant allSafe(boatConfig, limit)
    invariant boats == |boatConfig|
    decreases right - left + 1
  {
    if left == right {
      /* code modified by LLM (iteration 1): Single person case with proper multiset reasoning */
      var boat := [people[left]];
      assert sumBoat(boat) == people[left] <= limit;
      assert isSafeBoat(boat, limit);
      
      multisetRangeUpdate(people, left, right, boat);
      
      var oldBoatConfig := boatConfig;
      boatConfig := boatConfig + [boat];
      multisetAddAppend(oldBoatConfig, [boat]);
      multisetAddSingle(boat);
      
      boats := boats + 1;
      left := left + 1;
    } else if people[left] + people[right] <= limit {
      /* code modified by LLM (iteration 1): Two person case with proper multiset reasoning */
      var boat := [people[left], people[right]];
      assert sumBoat(boat) == people[left] + people[right] <= limit;
      assert |boat| == 2;
      assert isSafeBoat(boat, limit);
      
      multisetRangeUpdate(people, left, right, boat);
      
      var oldBoatConfig := boatConfig;
      boatConfig := boatConfig + [boat];
      multisetAddAppend(oldBoatConfig, [boat]);
      multisetAddSingle(boat);
      
      boats := boats + 1;
      left := left + 1;
      right := right - 1;
    } else {
      /* code modified by LLM (iteration 1): Heavy person case with proper multiset reasoning */
      var boat := [people[right]];
      assert sumBoat(boat) == people[right] <= limit;
      assert isSafeBoat(boat, limit);
      
      assert people[left..right+1] == people[left..right] + [people[right]];
      assert multiset(people[left..right+1]) == multiset(people[left..right]) + multiset{people[right]};
      assert multiset(boat) == multiset{people[right]};
      
      var oldBoatConfig := boatConfig;
      boatConfig := boatConfig + [boat];
      multisetAddAppend(oldBoatConfig, [boat]);
      multisetAddSingle(boat);
      
      boats := boats + 1;
      right := right - 1;
    }
  }
  
  /* code modified by LLM (iteration 1): Final assertions to establish postcondition */
  assert left > right;
  assert multisetAdd(boatConfig) == multiset(people);
  assert multisetEqual(boatConfig, people);
}