//ATOM 

function sumBoat(s: seq<nat>): nat 
    requires 1 <= |s| <= 2
{
    if |s| == 1 then s[0] else s[0] + s[1]
}


//ATOM 

predicate isSafeBoat(boat: seq<nat>, limit: nat) {
    1 <= |boat| <= 2 && sumBoat(boat) <= limit
}


//ATOM 

function multisetAdd(ss: seq<seq<nat>>): multiset<nat> {
    if ss == [] then multiset{} else multiset(ss[0]) + multisetAdd(ss[1..])
}


//ATOM 

predicate multisetEqual(ss: seq<seq<nat>>, xs: seq<nat>) {
    multiset(xs) == multisetAdd(ss)
}


//ATOM 

predicate allSafe(boats: seq<seq<nat>>, limit: nat) {
    forall boat :: boat in boats ==> isSafeBoat(boat, limit)
}


//ATOM 

predicate sorted(list: seq<int>)
{
    forall i,j :: 0 <= i < j < |list| ==> list[i] <= list[j]
}


//IMPL numRescueBoats

method numRescueBoats(people: seq<nat>, limit: nat) returns (boats: nat)
    requires |people| >= 1
    requires sorted(people)
    requires forall i: nat :: i < |people| ==> 1 <= people[i] <= limit
    ensures exists boatConfig: seq<seq<nat>> :: multisetEqual(boatConfig, people) && allSafe(boatConfig, limit) && boats == |boatConfig|// && forall boatConfigs :: multisetEqual(boatConfigs, people) && allSafe(boatConfigs, limit) ==> boats <= |boatConfigs|
{
    var left := 0;
    var right := |people| - 1;
    boats := 0;
    var boatConfig: seq<seq<nat>> := [];
    
    while left <= right
        invariant 0 <= left <= |people|
        invariant -1 <= right < |people|
        /* code modified by LLM (iteration 2): Fixed multiset invariant to properly handle remaining elements */
        invariant left > right ==> multisetAdd(boatConfig) == multiset(people)
        invariant left <= right ==> multisetAdd(boatConfig) + multiset(people[left..right+1]) == multiset(people)
        invariant allSafe(boatConfig, limit)
        invariant boats == |boatConfig|
    {
        if left == right {
            // Single person left
            var boat := [people[left]];
            
            /* code modified by LLM (iteration 2): Added safety proof for single person boat */
            assert isSafeBoat(boat, limit) by {
                assert 1 <= |boat| <= 2;
                assert sumBoat(boat) == people[left] <= limit;
            }
            
            /* code modified by LLM (iteration 2): Prove multiset equality step by step */
            assert people[left..right+1] == [people[left]];
            assert multiset(people[left..right+1]) == multiset{people[left]};
            assert multiset(boat) == multiset{people[left]};
            
            boatConfig := boatConfig + [boat];
            
            /* code modified by LLM (iteration 2): Prove multiset invariant after adding boat */
            assert multisetAdd(boatConfig) == multisetAdd(old(boatConfig)) + multiset(boat);
            assert multisetAdd(boatConfig) == multisetAdd(old(boatConfig)) + multiset(people[left..right+1]);
            assert multisetAdd(boatConfig) == multiset(people);
            
            boats := boats + 1;
            left := left + 1;
            
        } else if people[left] + people[right] <= limit {
            // Both can fit in one boat
            var boat := [people[left], people[right]];
            
            /* code modified by LLM (iteration 2): Added safety proof for two-person boat */
            assert isSafeBoat(boat, limit) by {
                assert 1 <= |boat| <= 2;
                assert sumBoat(boat) == people[left] + people[right] <= limit;
            }
            
            /* code modified by LLM (iteration 2): Detailed multiset reasoning for two-person case */
            var oldLeft := left;
            var oldRight := right;
            
            assert multiset(boat) == multiset{people[left], people[right]};
            assert people[left..right+1] == [people[left]] + people[left+1..right+1];
            assert people[left+1..right+1] == people[left+1..right] + [people[right]];
            assert multiset(people[left..right+1]) == multiset{people[left]} + multiset(people[left+1..right]) + multiset{people[right]};
            assert multiset(people[left..right+1]) == multiset(boat) + multiset(people[left+1..right]);
            
            boatConfig := boatConfig + [boat];
            boats := boats + 1;
            left := left + 1;
            right := right - 1;
            
            /* code modified by LLM (iteration 2): Prove invariant after updates */
            assert multiset(people[left..right+1]) == multiset(people[oldLeft+1..oldRight]);
            assert multisetAdd(boatConfig) == multisetAdd(old(boatConfig)) + multiset(boat);
            
        } else {
            // Only the heavier person (right) goes in this boat
            var boat := [people[right]];
            
            /* code modified by LLM (iteration 2): Added safety proof for heavy person boat */
            assert isSafeBoat(boat, limit) by {
                assert 1 <= |boat| <= 2;
                assert sumBoat(boat) == people[right] <= limit;
            }
            
            /* code modified by LLM (iteration 2): Detailed multiset reasoning for single heavy person */
            var oldRight := right;
            
            assert multiset(boat) == multiset{people[right]};
            assert people[left..right+1] == people[left..right] + [people[right]];
            assert multiset(people[left..right+1]) == multiset(people[left..right]) + multiset{people[right]};
            assert multiset(people[left..right+1]) == multiset(people[left..right]) + multiset(boat);
            
            boatConfig := boatConfig + [boat];
            boats := boats + 1;
            right := right - 1;
            
            /* code modified by LLM (iteration 2): Prove invariant after updates */
            assert multiset(people[left..right+1]) == multiset(people[left..oldRight]);
            assert multisetAdd(boatConfig) == multisetAdd(old(boatConfig)) + multiset(boat);
        }
    }
    
    /* code modified by LLM (iteration 2): Final assertion to establish postcondition */
    assert left > right;
    assert multisetAdd(boatConfig) == multiset(people);
    assert multisetEqual(boatConfig, people);
}