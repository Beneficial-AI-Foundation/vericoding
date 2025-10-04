// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs_spec(x: int) -> int {
    if x < 0 { -x } else { x }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn three_sum_closest(nums: Vec<i32>, target: i32) -> (result: i32)
    requires nums.len() >= 3,
    ensures 
        (exists|i: int, j: int, k: int| 
            0 <= i < j && j < k && k < nums.len() && 
            result == nums[i] + nums[j] + nums[k])
        &&
        (forall|i: int, j: int, k: int| 
            (0 <= i < j && j < k && k < nums.len()) ==>
            abs_spec(result - target) <= abs_spec(nums[i] + nums[j] + nums[k] - target))
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
    // let result1 = three_sum_closest(vec![-4, -1, 1, 2], 1);
    // println!("Result: {}", result1);
    
    // let result2 = three_sum_closest(vec![1, 1, 1, 0], 100);
    // println!("Result: {}", result2);
    
    // let result3 = three_sum_closest(vec![0, 2, 1, -3], 1);
    // println!("Result: {}", result3);
}