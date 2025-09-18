// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): find index returning nums.len() if not found */
fn find_index(nums: &Vec<i32>, x: i32) -> usize
{
    let mut i: usize = 0;
    while i < nums.len() && nums[i] != x
        invariant
            i <= nums.len(),
        decreases nums.len() - i
    {
        i = i + 1;
    }
    i
}
// </vc-helpers>

// <vc-spec>
fn next_greater_element(nums1: &Vec<i32>, nums2: &Vec<i32>) -> (result: Vec<i32>)
    requires
        forall|i: int, j: int| 0 <= i < nums1.len() && 0 <= j < nums1.len() && i != j ==> nums1[i] != nums1[j],
        forall|i: int, j: int| 0 <= i < nums2.len() && 0 <= j < nums2.len() && i != j ==> nums2[i] != nums2[j],
    ensures
        result.len() == nums1.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): ensure inner loop measure decreases by always incrementing k */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < nums1.len()
        invariant
            i <= nums1.len(),
            result.len() == i,
        decreases nums1.len() - i
    {
        let x: i32 = nums1[i];
        let mut j: usize = 0;
        while j < nums2.len() && nums2[j] != x
            invariant
                j <= nums2.len(),
            decreases nums2.len() - j
        {
            j = j + 1;
        }
        let mut next: i32 = -1;
        if j < nums2.len() {
            let mut k: usize = j + 1;
            let mut found: bool = false;
            while k < nums2.len() && !found
                invariant
                    j + 1 <= k,
                    k <= nums2.len(),
                decreases nums2.len() - k
            {
                if nums2[k] > x {
                    next = nums2[k];
                    found = true;
                    k = k + 1;
                } else {
                    k = k + 1;
                }
            }
        }
        result.push(next);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}