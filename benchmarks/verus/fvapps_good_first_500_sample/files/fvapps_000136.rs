// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn get_max_len(nums: Vec<i32>) -> (result: usize)
    ensures 
        result <= nums.len(),
        (forall|x: i32| nums@.contains(x) && x == 0) ==> result == 0,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {
    // Apps difficulty: interview
    // Assurance level: unguarded

    // assert(get_max_len(vec![1, -2, -3, 4]) == 4);
    // assert(get_max_len(vec![0, 1, -2, -3, -4]) == 3);
    // assert(get_max_len(vec![-1, -2, -3, 0, 1]) == 2);
}