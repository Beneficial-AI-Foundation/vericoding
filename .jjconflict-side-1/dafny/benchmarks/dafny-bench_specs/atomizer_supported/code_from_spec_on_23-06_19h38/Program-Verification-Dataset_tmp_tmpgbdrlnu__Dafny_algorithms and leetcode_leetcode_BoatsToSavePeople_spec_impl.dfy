// ATOM 

function sumBoat(s: seq<nat>): nat 
    requires 1 <= |s| <= 2
{
    if |s| == 1 then s[0] else s[0] + s[1]
}


// ATOM 

predicate isSafeBoat(boat: seq<nat>, limit: nat) {
    1 <= |boat| <= 2 && sumBoat(boat) <= limit
}


// ATOM 

function multisetAdd(ss: seq<seq<nat>>): multiset<nat> {
    if ss == [] then multiset{} else multiset(ss[0]) + multisetAdd(ss[1..])
}


// ATOM 

predicate multisetEqual(ss: seq<seq<nat>>, xs: seq<nat>) {
    multiset(xs) == multisetAdd(ss)
}


// ATOM 

predicate allSafe(boats: seq<seq<nat>>, limit: nat) {
    forall boat :: boat in boats ==> isSafeBoat(boat, limit)
}


// ATOM 

predicate sorted(list: seq<int>)
{
    forall i,j :: 0 <= i < j < |list| ==> list[i] <= list[j]
}


// IMPL numRescueBoats

/* code modified by LLM (iteration 4): Added helper lemma for multiset addition properties */
lemma multisetAddAppend(config: seq<seq<nat>>, boat: seq<nat>)
    ensures multisetAdd(config + [boat]) == multisetAdd(config) + multiset(boat)
{
    if config == [] {
        assert config + [boat] == [boat];
        assert multisetAdd([boat]) == multiset(boat);
        assert multisetAdd(config) == multiset{};
    } else {
        assert config + [boat] == [config[0]] + (config[1..] + [boat]);
        multisetAddAppend(config[1..], boat);
    }
}

/* code modified by LLM (iteration 4): Added helper lemma for sequence slicing */
lemma sequenceSliceProperty(people: seq<nat>, lower: int, upper: int)
    requires 0 <= lower <= upper < |people|
    ensures multiset(people[lower..upper+1]) == multiset{people[lower]} + multiset(people[lower+1..upper+1])
    ensures multiset(people[lower..upper+1]) == multiset(people[lower..upper]) + multiset{people[upper]}
{
    // Dafny proves this automatically
}

method numRescueBoats(people: seq<nat>, limit: nat) returns (boats: nat)
    requires |people| >= 1
    requires sorted(people)
    requires forall i: nat :: i < |people| ==> 1 <= people[i] <= limit
    ensures exists boatConfig: seq<seq<nat>> :: multisetEqual(boatConfig, people) && allSafe(boatConfig, limit) && boats == |boatConfig|
{
    var lower := 0;
    var upper := |people| - 1;
    var boatConfig: seq<seq<nat>> := [];
    boats := 0;
    
    while lower <= upper
        /* code modified by LLM (iteration 4): Fixed loop invariants with proper bounds */
        invariant 0 <= lower <= |people|
        invariant -1 <= upper < |people|
        invariant lower > upper ==> lower == upper + 1
        invariant lower <= upper ==> multisetAdd(boatConfig) + multiset(people[lower..upper+1]) == multiset(people)
        invariant lower > upper ==> multisetAdd(boatConfig) == multiset(people)
        invariant allSafe(boatConfig, limit)
        invariant boats == |boatConfig|
        decreases upper - lower + 1
    {
        if lower == upper {
            // One person left
            var boat := [people[lower]];
            
            /* code modified by LLM (iteration 4): Verify boat safety */
            assert isSafeBoat(boat, limit);
            
            /* code modified by LLM (iteration 4): Prove multiset equality before update */
            multisetAddAppend(boatConfig, boat);
            assert multiset(people[lower..upper+1]) == multiset{people[lower]};
            assert multiset(boat) == multiset{people[lower]};
            
            boatConfig := boatConfig + [boat];
            boats := boats + 1;
            lower := lower + 1;
            
        } else if people[lower] + people[upper] <= limit {
            // Two people can share a boat
            var boat := [people[lower], people[upper]];
            
            /* code modified by LLM (iteration 4): Verify boat safety */
            assert |boat| == 2;
            assert sumBoat(boat) == people[lower] + people[upper] <= limit;
            assert isSafeBoat(boat, limit);
            
            /* code modified by LLM (iteration 4): Prove multiset equality before update */
            multisetAddAppend(boatConfig, boat);
            sequenceSliceProperty(people, lower, upper);
            assert multiset(people[lower..upper+1]) == multiset{people[lower]} + multiset(people[lower+1..upper+1]);
            assert multiset(people[lower+1..upper+1]) == multiset(people[lower+1..upper]) + multiset{people[upper]};
            assert multiset(boat) == multiset{people[lower], people[upper]} == multiset{people[lower]} + multiset{people[upper]};
            
            boatConfig := boatConfig + [boat];
            boats := boats + 1;
            lower := lower + 1;
            upper := upper - 1;
            
        } else {
            // Heaviest person needs their own boat
            var boat := [people[upper]];
            
            /* code modified by LLM (iteration 4): Verify boat safety */
            assert isSafeBoat(boat, limit);
            
            /* code modified by LLM (iteration 4): Prove multiset equality before update */
            multisetAddAppend(boatConfig, boat);
            sequenceSliceProperty(people, lower, upper);
            assert multiset(people[lower..upper+1]) == multiset(people[lower..upper]) + multiset{people[upper]};
            assert multiset(boat) == multiset{people[upper]};
            
            boatConfig := boatConfig + [boat];
            boats := boats + 1;
            upper := upper - 1;
        }
    }
    
    /* code modified by LLM (iteration 4): Final verification that postcondition holds */
    assert lower > upper;
    assert multisetAdd(boatConfig) == multiset(people);
    assert multisetEqual(boatConfig, people);
}