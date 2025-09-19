// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn min_element_in_seq(nums: Seq<i32>) -> i32
    decreases nums.len()
{
    if nums.len() == 0 {
        0  // placeholder for empty sequence
    } else if nums.len() == 1 {
        nums[0]
    } else {
        if nums[0] <= min_element_in_seq(nums.skip(1)) {
            nums[0]
        } else {
            min_element_in_seq(nums.skip(1))
        }
    }
}

fn find_min(nums: Vec<i32>) -> (result: i32)
    requires nums.len() > 0,
    ensures 
        result == min_element_in_seq(nums@),
        forall|i: int| 0 <= i < nums.len() ==> result <= nums[i],
        exists|i: int| 0 <= i < nums.len() && result == nums[i],
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
    // let test1 = vec![1, 3, 5];
    // println!("Test 1: {}", find_min(test1));
    
    // let test2 = vec![2, 2, 2, 0, 1];
    // println!("Test 2: {}", find_min(test2));
    
    // let test3 = vec![4, 5, 6, 7, 0, 1, 2];
    // println!("Test 3: {}", find_min(test3));
}