// <vc-preamble>
use vstd::prelude::*;

verus! {

    spec fn is_valid_placement(rooms: Seq<char>, k: int, placement: Seq<int>) -> bool {
        placement.len() == k + 1 &&
        (forall|i: int| 0 <= i < placement.len() ==> 0 <= placement[i] < rooms.len()) &&
        (forall|i: int| 0 <= i < placement.len() ==> rooms[placement[i]] == '0') &&
        (forall|i: int, j: int| 0 <= i < j < placement.len() ==> placement[i] != placement[j]) &&
        (forall|i: int| 0 <= i < placement.len() - 1 ==> placement[i] < placement[i+1])
    }
spec fn optimal_max_distance(placement: Seq<int>) -> int {
    if placement.len() == 0 {
        0
    } else {
        placement[0]
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, k: int, rooms: Seq<char>) -> (result: int)
    requires 
        n > 0 &&
        k > 0 &&
        k < n &&
        rooms.len() == n &&
        (forall|i: int| 0 <= i < n ==> rooms[i] == '0' || rooms[i] == '1') &&
        exists|count: int| count >= k + 1 && count == (Set::new(|i: int| 0 <= i < n && rooms[i] == '0')).len()
    ensures 
        result >= 0 &&
        exists|placement: Seq<int>| is_valid_placement(rooms, k, placement) && optimal_max_distance(placement) == result
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}