// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn can_cross(stones: Vec<nat>) -> (result: bool)
    ensures
        stones.len() == 0 ==> result == false,
        stones.len() == 1 ==> result == true,
        stones.len() >= 2 && stones[0] != 0 ==> result == false,
        result == true || result == false
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    false
    // impl-end
}
// </vc-code>


}
fn main() {
    // // Apps difficulty: interview
    // // Assurance level: unguarded

    // assert(can_cross(vec![0, 1, 3, 5, 6, 8, 12, 17]) == true);
    // assert(can_cross(vec![0, 1, 2, 3, 4, 8, 9, 11]) == false);
    // assert(can_cross(vec![0, 1, 3, 4, 5, 7, 9, 10, 12]) == true);
}