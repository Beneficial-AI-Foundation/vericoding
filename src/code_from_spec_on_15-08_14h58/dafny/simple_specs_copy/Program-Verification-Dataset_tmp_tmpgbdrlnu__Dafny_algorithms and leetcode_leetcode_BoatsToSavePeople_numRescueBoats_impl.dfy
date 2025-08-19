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

/* code modified by LLM (iteration 1): added helper lemma to prove multiset properties */
lemma multisetAddProperty(config: seq<seq<nat>>, newBoat: seq<nat>)
  ensures multisetAdd(config + [newBoat]) == multisetAdd(config) + multiset(newBoat)
{
  if config == [] {
    assert config + [newBoat] == [newBoat];
    assert multisetAdd([newBoat]) == multiset(newBoat);
  } else {
    assert (config + [newBoat])[0] == config[0];
    assert (config + [newBoat])[1..] == config[1..] + [newBoat];
    multisetAddProperty(config[1..], newBoat);
  }
}

/* code modified by LLM (iteration 1): fixed helper lemma with correct preconditions */
lemma sliceProperty(people: seq<nat>, left: int, right: int)
  requires 0 <= left <= right < |people|
  ensures multiset(people[left..right+1]) == multiset([people[left]]) + multiset(people[left+1..right+1])
  ensures multiset(people[left..right+1]) == multiset(people[left..right]) + multiset([people[right]])
{
  // Dafny can prove these automatically with the slice properties
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
  var config: seq<seq<nat>> := [];
  
  /* code modified by LLM (iteration 1): added assertion using sequence equality */
  assert people[0..|people|] == people;
  assert multiset(people[0..|people|]) == multiset(people);
  
  while left <= right
    invariant 0 <= left <= |people|
    invariant -1 <= right < |people|
    invariant multisetAdd(config) + (if left <= right then multiset(people[left..right+1]) else multiset{}) == multiset(people)
    invariant left > right ==> multisetEqual(config, people)
    invariant allSafe(config, limit)
    invariant boats == |config|
  {
    if left == right {
      /* code modified by LLM (iteration 1): added assertions to prove invariant maintenance */
      var newBoat := [people[left]];
      assert multiset(people[left..right+1]) == multiset([people[left]]);
      multisetAddProperty(config, newBoat);
      
      config := config + [newBoat];
      boats := boats + 1;
      left := left + 1;
      
      /* code modified by LLM (iteration 1): assert final state after left > right */
      assert left > right;
      assert multisetAdd(config) + multiset{} == multiset(people);
    } else if people[left] + people[right] <= limit {
      /* code modified by LLM (iteration 1): added bounds check and assertions to prove invariant maintenance */
      assert left < right;
      sliceProperty(people, left, right);
      
      var newBoat := [people[left], people[right]];
      assert multiset(people[left..right+1]) == multiset([people[left]]) + multiset(people[left+1..right+1]);
      /* code modified by LLM (iteration 1): added manual proof for the slice property when left+1 <= right */
      if left + 1 <= right {
        assert multiset(people[left+1..right+1]) == multiset(people[left+1..right]) + multiset([people[right]]);
      } else {
        assert left + 1 == right + 1;
        assert people[left+1..right+1] == [];
        assert people[left+1..right] == [];
      }
      multisetAddProperty(config, newBoat);
      
      config := config + [newBoat];
      boats := boats + 1;
      left := left + 1;
      right := right - 1;
    } else {
      /* code modified by LLM (iteration 1): added bounds check and assertions to prove invariant maintenance */
      assert left < right;
      sliceProperty(people, left, right);
      
      var newBoat := [people[right]];
      multisetAddProperty(config, newBoat);
      
      config := config + [newBoat];
      boats := boats + 1;
      right := right - 1;
    }
  }
}