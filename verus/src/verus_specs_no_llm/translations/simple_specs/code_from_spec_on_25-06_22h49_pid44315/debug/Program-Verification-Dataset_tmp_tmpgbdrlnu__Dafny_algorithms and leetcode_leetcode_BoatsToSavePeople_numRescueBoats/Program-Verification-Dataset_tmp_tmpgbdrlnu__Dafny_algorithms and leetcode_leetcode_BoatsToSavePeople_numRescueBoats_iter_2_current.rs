use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted(list: Seq<int>) -> bool {
    forall|i:int,j:int| 0 <= i < j < list.len() ==> list.spec_index(i) <= list.spec_index(j)
}

spec fn sumBoat(boat: Seq<nat>) -> nat {
    if boat.len() == 0 {
        0
    } else {
        boat.spec_index(0) + sumBoat(boat.subrange(1, boat.len() as int))
    }
}

spec fn isSafeBoat(boat: Seq<nat>, limit: nat) -> bool {
    1 <= boat.len() <= 2 && sumBoat(boat) <= limit
}

spec fn allSafe(boats: Seq<Seq<nat>>, limit: nat) -> bool {
    forall|boat| boats.contains(boat) ==> isSafeBoat(boat, limit)
}

spec fn multisetAdd(ss: Seq<Seq<nat>>) -> Multiset<nat> {
    if ss.len() == 0 {
        Multiset::empty()
    } else {
        multiset(ss.spec_index(0)).add(multisetAdd(ss.subrange(1, ss.len() as int)))
    }
}

spec fn multisetEqual(ss: Seq<Seq<nat>>, xs: Seq<nat>) -> bool {
    multiset(xs) == multisetAdd(ss)
}

// Helper function to construct a valid boat configuration
spec fn constructBoats(people: Seq<nat>, limit: nat, left: int, right: int, boats: Seq<Seq<nat>>) -> Seq<Seq<nat>>
    decreases right - left + 1
{
    if left > right {
        boats
    } else if left == right {
        boats.push(seq![people.spec_index(left)])
    } else {
        if people.spec_index(left) + people.spec_index(right) <= limit {
            constructBoats(people, limit, left + 1, right - 1, 
                boats.push(seq![people.spec_index(left), people.spec_index(right)]))
        } else {
            constructBoats(people, limit, left, right - 1,
                boats.push(seq![people.spec_index(right)]))
        }
    }
}

fn numRescueBoats(people: Seq<nat>, limit: nat) -> (boats: nat)
    requires
        people.len() >= 1,
        sorted(people),
        forall|i: nat| i < people.len() ==> 1 <= people.spec_index(i) <= limit
    ensures
        exists|boatConfig: Seq<Seq<nat>>| multisetEqual(boatConfig, people) && allSafe(boatConfig, limit) && boats == boatConfig.len()
{
    let mut left: int = 0;
    let mut right: int = (people.len() - 1) as int;
    let mut count = 0;
    
    while left <= right 
        invariant
            0 <= left <= people.len(),
            -1 <= right < people.len(),
            left <= right + 1,
            count >= 0,
    {
        if left == right {
            count = count + 1;
            left = left + 1;
        } else {
            if people.spec_index(left) + people.spec_index(right) <= limit {
                left = left + 1;
            }
            right = right - 1;
            count = count + 1;
        }
    }
    
    // Proof that our construction satisfies the postcondition
    proof {
        let boatConfig = constructBoats(people, limit, 0, (people.len() - 1) as int, seq![]);
        assert(boatConfig.len() == count);
        assert(multisetEqual(boatConfig, people));
        assert(allSafe(boatConfig, limit));
    }
    
    count
}

}