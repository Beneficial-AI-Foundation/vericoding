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

fn numRescueBoats(people: Seq<nat>, limit: nat) -> (boats: nat)
    requires
        people.len() >= 1,
        sorted(people),
        forall|i: nat| i < people.len() ==> 1 <= people.spec_index(i) <= limit
    ensures
        exists|boatConfig: Seq<Seq<nat>>| multisetEqual(boatConfig, people) && allSafe(boatConfig, limit) && boats == boatConfig.len()
{
    let mut left = 0;
    let mut right = people.len() - 1;
    let mut count = 0;
    
    while left <= right 
        invariant
            left <= people.len(),
            right < people.len(),
            left <= right + 1,
    {
        if left == right {
            count = count + 1;
            break;
        }
        
        if people.spec_index(left) + people.spec_index(right) <= limit {
            left = left + 1;
        }
        right = right - 1;
        count = count + 1;
    }
    
    count
}

}

The key insights in this implementation:



   - Start with lightest person (left) and heaviest person (right)  
   - If they can share a boat (sum ≤ limit), advance both pointers
   - Otherwise, the heavy person goes alone, advance only right pointer
   - Each iteration uses one boat


This greedy approach is optimal because pairing the lightest remaining person with the heaviest remaining person (when possible) never prevents a better solution.