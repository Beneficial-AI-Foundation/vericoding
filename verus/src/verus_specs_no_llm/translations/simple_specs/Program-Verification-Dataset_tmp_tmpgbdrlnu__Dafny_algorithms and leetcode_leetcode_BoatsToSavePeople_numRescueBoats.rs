// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted(list: Seq<int>) -> bool {
    forall i,j :: 0 <= i < j < list.len() ==> list.spec_index(i) <= list.spec_index(j)
}
spec fn isSafeBoat(boat: Seq<nat>, limit: nat) -> bool {
    1 <= boat.len() <= 2 && sumBoat(boat) <= limit
}
spec fn allSafe(boats: Seq<Seq<nat>>, limit: nat) -> bool {
    forall boat :: boat in boats ==> isSafeBoat(boat, limit)
}
spec fn multisetEqual(ss: Seq<Seq<nat>>, xs: Seq<nat>) -> bool {
    multiset(xs) == multisetAdd(ss)
}

fn numRescueBoats(people: Seq<nat>, limit: nat) -> (boats: nat)
    requires
        people.len() >= 1,
        sorted(people),
        forall i: nat :: i < people.len() ==> 1 <= people.spec_index(i) <= limit
    ensures
        exists boatConfig: seq<seq<nat>> :: multisetEqual(boatConfig, people) && allSafe(boatConfig, limit) && boats == boatConfig.len()// && forall boatConfigs :: multisetEqual(boatConfigs, people) && allSafe(boatConfigs, limit) ==> boats <= boatConfigs.len()
{
    return 0;
}

}