// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn isSafeBoat(boat: Seq<nat>, limit: nat) -> bool {
    1 <= boat.len() <= 2 and sumBoat(boat) <= limit
}
spec fn multisetEqual(ss: Seq<Seq<nat>>, xs: Seq<nat>) -> bool {
    multiset(xs) == multisetAdd(ss)
}
spec fn allSafe(boats: Seq<Seq<nat>>, limit: nat) -> bool {
    forall|boat: int| boat in boats ==> isSafeBoat(boat, limit)
}
spec fn sorted(list: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < list.len() ==> list[i] <= list[j]
}

fn numRescueBoats(people: Seq<nat>, limit: nat) -> (boats: nat)
    requires people.len() >= 1,
             sorted(people),
             forall i: nat :: i < people.len() ==> 1 <= people[i] <= limit
    ensures exists boatConfig: seq<seq<nat>> :: multisetEqual(boatConfig, people) and allSafe(boatConfig, limit) and boats == boatConfig.len()// and forall|boatConfigs: int| multisetEqual(boatConfigs, people) and allSafe(boatConfigs, limit) ==> boats <= boatConfigs.len()
{
}

}