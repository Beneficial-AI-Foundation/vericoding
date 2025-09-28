// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn remove_element(nums: &mut Vec<i32>, val: i32) -> (newLength: usize)
    ensures 
        0 <= newLength <= nums.len(),
        forall|i: int| 0 <= i < newLength ==> nums[i] != val,
        nums@.subrange(0, newLength as int).to_multiset() == 
            old(nums)@.to_multiset().remove(val),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): implemented correct two-pointer removal and corresponding invariants */
{
    let mut k: usize = 0;
    let mut i: usize = 0;

    while i < nums.len()
        invariant
            nums.len() == old(nums)@.len(),
            0 <= k <= i <= nums.len(),
            forall|j: int| 0 <= j < k ==> nums@[j] != val,
            nums@.subrange(0, k as int).to_multiset() == old(nums)@.subrange(0, i as int).to_multiset().remove(val),
            forall|j: int| i <= j < nums.len() ==> nums@[j] == old(nums)@[j],
        decreases nums.len() - i
    {
        if nums[i] != val {
            nums[k] = nums[i];
            k = k + 1;
        }
        i = i + 1;
    }
    k
}
// </vc-code>

}
fn main() {}