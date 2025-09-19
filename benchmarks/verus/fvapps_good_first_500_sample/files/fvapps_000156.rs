// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn constrained_max_subset_sum(nums: Vec<i32>, k: usize) -> (result: i32)
    requires 
        nums.len() > 0,
        k > 0,
        k <= nums.len(),
    ensures 
        exists|x: i32| nums@.contains(x) && result >= x,
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

    // println!("{}", constrained_max_subset_sum(vec![10, 2, -10, 5, 20], 2));
    // println!("{}", constrained_max_subset_sum(vec![-1, -2, -3], 1));
    // println!("{}", constrained_max_subset_sum(vec![10, -2, -10, -5, 20], 2));
}