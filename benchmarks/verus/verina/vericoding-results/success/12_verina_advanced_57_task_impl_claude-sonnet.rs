// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): helper to check valid index bounds */
fn valid_index(vec: &Vec<i32>, i: usize) -> bool
{
    i < vec.len()
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
    /* code modified by LLM (iteration 3): fixed index bounds and invariant conditions */
    let mut result = Vec::new();
    
    for i in 0..nums1.len()
        invariant
            result.len() == i,
    {
        let mut found = -1;
        let mut j = 0;
        let mut found_match = false;
        
        while j < nums2.len()
            invariant
                0 <= j <= nums2.len(),
                i < nums1.len(),
                !found_match ==> found == -1,
            decreases nums2.len() - j
        {
            if nums2[j] == nums1[i] {
                found_match = true;
                let mut k = j + 1;
                while k < nums2.len()
                    invariant
                        j < k <= nums2.len(),
                        i < nums1.len(),
                    decreases nums2.len() - k
                {
                    if nums2[k] > nums1[i] {
                        found = nums2[k];
                        break;
                    }
                    k += 1;
                }
                break;
            }
            j += 1;
        }
        
        result.push(found);
    }
    
    result
}
// </vc-code>

}
fn main() {}