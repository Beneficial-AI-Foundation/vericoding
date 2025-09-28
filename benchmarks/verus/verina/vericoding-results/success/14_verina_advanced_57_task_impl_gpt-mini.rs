// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): use usize indices and return Option<usize> when not found */
fn find_index(nums: &Vec<i32>, val: i32) -> Option<usize> {
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            i <= nums.len(),
        decreases nums.len() - i
    {
        if nums[i] == val {
            return Some(i);
        }
        i += 1;
    }
    None
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
    /* code modified by LLM (iteration 3): search nums2 linearly to find next greater without index arithmetic */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < nums1.len()
        invariant
            i <= nums1.len(),
            result.len() == i,
        decreases nums1.len() - i
    {
        let cur = nums1[i];
        let mut ng: i32 = -1;
        let mut started: bool = false;
        let mut j: usize = 0;
        while j < nums2.len() && ng == -1
            invariant
                j <= nums2.len(),
            decreases nums2.len() - j
        {
            if !started {
                if nums2[j] == cur {
                    started = true;
                }
            } else {
                if nums2[j] > cur {
                    ng = nums2[j];
                }
            }
            j += 1;
        }
        result.push(ng);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}