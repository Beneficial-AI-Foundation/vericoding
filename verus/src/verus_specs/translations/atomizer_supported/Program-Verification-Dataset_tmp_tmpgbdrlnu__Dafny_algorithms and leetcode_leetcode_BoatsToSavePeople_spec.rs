use vstd::prelude::*;

verus! {

// ATOM 
spec fn sumBoat(s: Seq<nat>) -> nat 
    recommends 1 <= s.len() <= 2
{
    if s.len() == 1 { s[0] } else { s[0] + s[1] }
}

// ATOM 
spec fn isSafeBoat(boat: Seq<nat>, limit: nat) -> bool {
    1 <= boat.len() <= 2 && sumBoat(boat) <= limit
}

// ATOM 
spec fn multisetAdd(ss: Seq<Seq<nat>>) -> Multiset<nat> {
    if ss == seq![] { 
        multiset!{} 
    } else { 
        ss[0].to_multiset() + multisetAdd(ss.subrange(1, ss.len() as int))
    }
}

// ATOM 
spec fn multisetEqual(ss: Seq<Seq<nat>>, xs: Seq<nat>) -> bool {
    xs.to_multiset() == multisetAdd(ss)
}

// ATOM 
spec fn allSafe(boats: Seq<Seq<nat>>, limit: nat) -> bool {
    forall|boat| boats.contains(boat) ==> isSafeBoat(boat, limit)
}

// ATOM 
spec fn sorted(list: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < list.len() ==> list[i] <= list[j]
}

// SPEC 
pub fn numRescueBoats(people: Seq<nat>, limit: nat) -> (boats: nat)
    requires(people.len() >= 1)
    requires(sorted(people))
    requires(forall|i: nat| i < people.len() ==> 1 <= people[i as int] <= limit)
    ensures(exists|boatConfig: Seq<Seq<nat>>| multisetEqual(boatConfig, people) && allSafe(boatConfig, limit) && boats == boatConfig.len())
{
}

}