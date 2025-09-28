// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helper functions needed for this fix */
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
    /* code modified by LLM (iteration 5): Fixed type mismatches in length invariants by casting usize to int, and added proof assertions to establish invariants for the remaining loops */
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0usize;
    let mut j = 0usize;
    while i < arr1.len() && j < arr2.len()
        invariant
            0 <= i <= arr1@.len(),
            0 <= j <= arr2@.len(),
            result@.len() == (i as int) + (j as int),
            forall |p: int, q: int| 0 <= p < q < result@.len() ==> result@[p] <= result@[q],
            forall |k: int, p: int| 0 <= k < result@.len() && (i as int) <= p < arr1@.len() ==> result@[k] <= arr1@[p],
            forall |k: int, p: int| 0 <= k < result@.len() && (j as int) <= p < arr2@.len() ==> result@[k] <= arr2@[p],
        decreases arr1@.len() - (i as int) + arr2@.len() - (j as int)
    {
        if arr1[i] <= arr2[j] {
            result.push(arr1[i]);
            i += 1;
        } else {
            result.push(arr2[j]);
            j += 1;
        }
    }
    proof {
        assert(forall |k: int| 0 <= k < result@.len() ==> result@[k] <= arr1@[i as int]);
    }
    while i < arr1.len()
        invariant
            i <= arr1@.len(),
            forall |p: int, q: int| 0 <= p < q < result@.len() ==> result@[p] <= result@[q],
            forall |k: int| 0 <= k < result@.len() ==> result@[k] <= arr1@[i as int],
        decreases arr1@.len() - (i as int)
    {
        result.push(arr1[i]);
        i += 1;
    }
    proof {
        assert(forall |k: int| 0 <= k < result@.len() ==> result@[k] <= arr2@[j as int]);
    }
    while j < arr2.len()
        invariant
            j <= arr2@.len(),
            forall |p: int, q: int| 0 <= p < q < result@.len() ==> result@[p] <= result@[q],
            forall |k: int| 0 <= k < result@.len() ==> result@[k] <= arr2@[j as int],
        decreases arr2@.len() - (j as int)
    {
        result.push(arr2[j]);
        j += 1;
    }
    result
}
// </vc-code>

}
fn main() {}