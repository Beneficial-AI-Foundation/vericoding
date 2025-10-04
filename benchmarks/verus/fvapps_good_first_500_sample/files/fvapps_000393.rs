// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn has_increasing_triplet_spec(nums: Seq<i32>) -> bool {
    exists|i: int, j: int, k: int| 
        0 <= i < j && j < k && k < nums.len() &&
        nums[i] < nums[j] && nums[j] < nums[k]
}

fn has_increasing_triplet(nums: Vec<i32>) -> (result: bool)
    ensures result == has_increasing_triplet_spec(nums@)
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
    // let test1 = vec![1, 2, 3, 4, 5];
    // println!("{}", has_increasing_triplet(test1));
    
    // let test2 = vec![5, 4, 3, 2, 1];
    // println!("{}", has_increasing_triplet(test2));
    
    // let test3 = vec![2, 1, 5, 0, 4, 6];
    // println!("{}", has_increasing_triplet(test3));
}