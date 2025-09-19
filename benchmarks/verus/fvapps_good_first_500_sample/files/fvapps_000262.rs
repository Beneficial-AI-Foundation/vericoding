// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn k_length_apart(nums: Vec<usize>, k: usize) -> (result: bool)
    requires 
        nums.len() >= 1,
        nums.len() <= 100000,
        k <= nums.len(),
        forall|i: int| 0 <= i < nums.len() ==> nums[i] <= 1,
    ensures
        result == true ==> (
            forall|i: int, j: int| 
                0 <= i < nums.len() && 0 <= j < nums.len() && 
                nums[i] == 1 && nums[j] == 1 && i < j ==> 
                j - i > k
        ),
        result == false ==> (
            exists|i: int, j: int| 
                0 <= i < nums.len() && 0 <= j < nums.len() && 
                nums[i] == 1 && nums[j] == 1 && i < j && 
                j - i <= k
        ),
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
    // let test1 = vec![1, 0, 0, 0, 1, 0, 0, 1];
    // let result1 = k_length_apart(test1, 2);
    // assert!(result1 == true);
    
    // let test2 = vec![1, 0, 0, 1, 0, 1];
    // let result2 = k_length_apart(test2, 2);
    // assert!(result2 == false);
    
    // let test3 = vec![0, 1, 0, 1];
    // let result3 = k_length_apart(test3, 1);
    // assert!(result3 == true);
}