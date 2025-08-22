/*
// SPEC 

method numRescueBoats(people: seq<nat>, limit: nat) returns (boats: nat)
    requires |people| >= 1
    requires sorted(people)
    requires forall i: nat :: i < |people| ==> 1 <= people[i] <= limit
    ensures exists boatConfig: seq<seq<nat>> :: multisetEqual(boatConfig, people) && allSafe(boatConfig, limit) && boats == |boatConfig|// && forall boatConfigs :: multisetEqual(boatConfigs, people) && allSafe(boatConfigs, limit) ==> boats <= |boatConfigs|
{
}

/*
limit 3
[3,2,2,1]
lower = 0
upper = 3

upper = 2
lower= 0

lower = 1
upper = 1

lower = 2 [..2]
upper = 1 [2..]
*/
;
nums[k++] = i+1;
// ATOM 
function binsort(nums: number[], limit: number) {
    let result = new Array(limit);
    result.fill(0);
    for(let i = 0; i < nums.length; i++) {
        result[nums[i]-1]++;
    }
    var k = 0;
    for(let i=0; i < result.length; i++) {
        for(let j = 0; j < result[i]; j++) {
            nums[k++] = i+1;
        }
    }
}
*/

*/

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


// SPEC 

method numRescueBoats(people: seq<nat>, limit: nat) returns (boats: nat)
    requires |people| >= 1
    requires sorted(people)
    requires forall i: nat :: i < |people| ==> 1 <= people[i] <= limit
    ensures exists boatConfig: seq<seq<nat>> :: multisetEqual(boatConfig, people) && allSafe(boatConfig, limit) && boats == |boatConfig|// && forall boatConfigs :: multisetEqual(boatConfigs, people) && allSafe(boatConfigs, limit) ==> boats <= |boatConfigs|
{
}

/*
limit 3
[3,2,2,1]
lower = 0
upper = 3

upper = 2
lower= 0

lower = 1
upper = 1

lower = 2 [..2]
upper = 1 [2..]
*/


/*
limit 3
[3,2,2,1]
lower = 0
upper = 3

upper = 2
lower= 0

lower = 1
upper = 1

lower = 2 [..2]
upper = 1 [2..]
*/


/*
limit 3
[3,2,2,1]
lower = 0
upper = 3

upper = 2
lower= 0

lower = 1
upper = 1

lower = 2 [..2]
upper = 1 [2..]
*/
