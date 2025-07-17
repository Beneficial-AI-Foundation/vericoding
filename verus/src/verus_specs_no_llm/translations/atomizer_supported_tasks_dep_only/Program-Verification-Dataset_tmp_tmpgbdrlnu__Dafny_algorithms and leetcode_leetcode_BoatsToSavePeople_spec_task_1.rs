// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isSafeBoat(boat: Seq<nat>, limit: nat) -> bool {
    1 <= boat.len() <= 2 && sumBoat(boat) <= limit
}
spec fn multisetEqual(ss: Seq<Seq<nat>>, xs: Seq<nat>) -> bool {
    multiset(xs) == multisetAdd(ss)
}
spec fn allSafe(boats: Seq<Seq<nat>>, limit: nat) -> bool {
    forall |boat: int| boat in boats ==> isSafeBoat(boat, limit)
}
spec fn sorted(list: Seq<int>) -> bool {
    forall |i: int, j: int| 0 <= i < j < list.len() ==> list.index(i) <= list.index(j)
}

spec fn sumBoat(s: Seq<nat>) -> nat
    requires
        1 <= s.len() <= 2
{
    0
}

spec fn spec_numRescueBoats(people: Seq<nat>, limit: nat) -> boats: nat
    requires
        people.len() >= 1,
        sorted(people),
        forall |i: nat| i < people.len() ==> 1 <= people.index(i) <= limit
    ensures
        exists |boatConfig: Seq<Seq<nat>>| multisetEqual(boatConfig, people) && allSafe(boatConfig, limit) && boats == boatConfig.len()// && forall |boatConfigs: int| multisetEqual(boatConfigs, people) && allSafe(boatConfigs, limit) ==> boats <= boatConfigs.len()
;

proof fn lemma_numRescueBoats(people: Seq<nat>, limit: nat) -> (boats: nat)
    requires
        people.len() >= 1,
        sorted(people),
        forall |i: nat| i < people.len() ==> 1 <= people.index(i) <= limit
    ensures
        exists |boatConfig: Seq<Seq<nat>>| multisetEqual(boatConfig, people) && allSafe(boatConfig, limit) && boats == boatConfig.len()// && forall |boatConfigs: int| multisetEqual(boatConfigs, people) && allSafe(boatConfigs, limit) ==> boats <= boatConfigs.len()
{
    0
}

}