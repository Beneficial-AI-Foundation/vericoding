// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_peak_element(nums: Vec<i32>) -> (result: i32)
    ensures 
        nums.len() == 0 ==> result == -1,
        nums.len() > 0 ==> (0 <= result && result < nums.len()),
        nums.len() == 1 ==> result == 0,
        (result == 0 && nums.len() > 1) ==> 
            (nums[0] >= nums[1]),
        (result == (nums.len() - 1) as i32 && nums.len() > 1) ==> 
            (nums[result as int] >= nums[(result - 1) as int]),
        (0 < result && (result as int) < nums.len() - 1) ==> 
            (nums[result as int] >= nums[(result - 1) as int] && nums[result as int] >= nums[(result + 1) as int])
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
    // let result1 = find_peak_element(vec![1, 2, 3, 1]);
    // let result2 = find_peak_element(vec![1]);
}