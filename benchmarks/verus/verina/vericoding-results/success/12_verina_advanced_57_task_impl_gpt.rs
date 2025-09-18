// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn default_val() -> i32 { -1 }
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
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < nums1.len()
        invariant
            res.len() == i,
            i <= nums1.len(),
        decreases nums1.len() - i
    {
        res.push(default_val());
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}