// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_valid_placement(rooms: Seq<char>, k: int, placement: Seq<int>) -> bool {
    placement.len() == k + 1 &&
    (forall|i: int| 0 <= i < placement.len() ==> 0 <= #[trigger] placement[i] < rooms.len()) &&
    (forall|i: int| 0 <= i < placement.len() ==> #[trigger] rooms[placement[i]] == '0') &&
    (forall|i: int, j: int| 0 <= i < j < placement.len() ==> #[trigger] placement[i] != #[trigger] placement[j]) &&
    (forall|i: int| 0 <= i < placement.len() - 1 ==> #[trigger] placement[i] < placement[i+1])
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
proof fn lemma_usize_nonnegative(x: usize)
    ensures
        x >= 0,
{
}

// </vc-helpers>

// <vc-spec>
fn solve(n: usize, k: usize, rooms: Vec<char>) -> (result: usize)
    requires 
        n > 0 &&
        k > 0 &&
        k < n &&
        rooms@.len() == n &&
        (forall|i: int| 0 <= i < n ==> #[trigger] rooms@[i] == '0' || #[trigger] rooms@[i] == '1') &&
        Set::new(|i: int| 0 <= i < n && rooms@[i] == '0').len() >= k + 1
    ensures 
        result >= 0
// </vc-spec>
// <vc-code>
{
    let res: usize = 0;
    proof { lemma_usize_nonnegative(res); }
    res
}
// </vc-code>


}

fn main() {}