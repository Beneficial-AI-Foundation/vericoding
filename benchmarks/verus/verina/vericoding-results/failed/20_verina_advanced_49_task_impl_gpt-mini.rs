// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): min for usize values */
fn min_usize(a: usize, b: usize) -> usize { if a < b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn merge_sorted_lists(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    requires 
        forall|i: int, j: int| 0 <= i < j < arr1.len() ==> arr1[i] <= arr1[j],
        forall|i: int, j: int| 0 <= i < j < arr2.len() ==> arr2[i] <= arr2[j],
    ensures
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        result.len() == arr1.len() + arr2.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): merge with invariants ensuring sortedness and length */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    while i < arr1.len() || j < arr2.len()
        invariant
            i <= arr1.len(),
            j <= arr2.len(),
            result.len() == i + j,
            forall|r: int, a: int| 0 <= r < result.len() && (i as int) <= a < arr1.len() ==> result[r as usize] <= arr1[a as usize],
            forall|r: int, b: int| 0 <= r < result.len() && (j as int) <= b < arr2.len() ==> result[r as usize] <= arr2[b as usize],
        decreases
            (arr1.len() as int + arr2.len() as int - (i + j) as int)
    {
        if i < arr1.len() && (j >= arr2.len() || arr1[i] <= arr2[j]) {
            let old_i = i;
            let old_len = result.len();
            result.push(arr1[old_i]);
            i = old_i + 1;
            proof {
                // result.len() updated correctly
                assert(result.len() == old_len + 1);
                assert(result.len() == i + j);
                // For previously existing elements, the tail bounds only shrink, so the old properties still hold
                assert(forall|r: int, a: int| 0 <= r < old_len && (old_i as int) <= a < arr1.len() ==> result[r as usize] <= arr1[a as usize]);
                assert(forall|r: int, b: int| 0 <= r < old_len && (j as int) <= b < arr2.len() ==> result[r as usize] <= arr2[b as usize]);
                // Now prove the property for the newly pushed element at index old_len
                // (1) against arr1 tail: arr1 is sorted, so arr1[old_i] <= arr1[a] for a >= i
                assert(forall|a: int| (i as int) <= a < arr1.len() ==> arr1[old_i] <= arr1[a as usize]);
                // (2) against arr2 tail: if j < arr2.len(), from branch condition arr1[old_i] <= arr2[j] and arr2 is sorted
                if j < arr2.len() {
                    assert(arr1[old_i] <= arr2[j]);
                    assert(forall|b: int| (j as int) <= b < arr2.len() ==> arr2[j] <= arr2[b as usize]);
                    assert(forall|b: int| (j as int) <= b < arr2.len() ==> arr1[old_i] <= arr2[b as usize]);
                }
                // Combine: the new element respects both tail properties
                assert(forall|r: int, a: int| 0 <= r < result.len() && (i as int) <= a < arr1.len() ==> result[r as usize] <= arr1[a as usize]);
                assert(forall|r: int, b: int| 0 <= r < result.len() && (j as int) <= b < arr2.len() ==> result[r as usize] <= arr2[b as usize]);
            }
        } else {
            let old_j = j;
            let old_len = result.len();
            result.push(arr2[old_j]);
            j = old_j + 1;
            proof {
                assert(result.len() == old_len + 1);
                assert(result.len() == i + j);
                assert(forall|r: int, b: int| 0 <= r < old_len && (old_j as int) <= b < arr2.len() ==> result[r as usize] <= arr2[b as usize]);
                assert(forall|r: int, a: int| 0 <= r < old_len && (i as int) <= a < arr1.len() ==> result[r as usize] <= arr1[a as usize]);
                // New element vs arr2 tail: sortedness of arr2
                assert(forall|b: int| (j as int) <= b < arr2.len() ==> arr2[old_j] <= arr2[b as usize]);
                // New element vs arr1 tail: if i < arr1.len(), from branch condition we know arr2[old_j] < arr1[i] or arr1[i] > arr2[old_j]
                if i < arr1.len() {
                    // From the branch choice, arr2[old_j] < arr1[i] or arr1[i] > arr2[old_j], and arr1 sorted gives arr1[i] <= arr1[a]
                    // Hence arr2[old_j] <= arr1[a] for all a >= i
                    assert(forall|a: int| (i as int) <= a < arr1.len() ==> arr2[old_j] <= arr1[a as usize]);
                }
                // Combine to restore invariants
                assert(forall|r: int, a: int| 0 <= r < result.len() && (i as int) <= a < arr1.len() ==> result[r as usize] <= arr1[a as usize]);
                assert(forall|r: int, b: int| 0 <= r < result.len() && (j as int) <= b < arr2.len() ==> result[r as usize] <= arr2[b as usize]);
            }
        }
    }
    result
}
// </vc-code>

}
fn main() {}