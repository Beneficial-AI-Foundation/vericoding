// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn remove_duplicates(nums: &Vec<i32>) -> (result: usize)
    requires forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] <= nums[j],
    ensures result <= nums.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added decreases clause to fix loop verification */
    if nums.len() == 0 {
        return 0;
    }
    
    // Since we cannot modify the immutable vector, we can only count unique elements
    let mut count: usize = 1;
    let mut i: usize = 1;
    
    while i < nums.len()
        invariant
            1 <= count <= i,
            i <= nums.len(),
            count <= nums.len(),
        decreases nums.len() - i
    {
        if nums[i] != nums[i - 1] {
            count = count + 1;
        }
        i = i + 1;
    }
    
    count
}
// </vc-code>

}
fn main() {}