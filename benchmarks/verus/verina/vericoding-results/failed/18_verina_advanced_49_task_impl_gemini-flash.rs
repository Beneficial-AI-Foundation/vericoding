// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The previous helper section was empty, so it is kept empty as no helper functions are needed for this problem. */
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
/* code modified by LLM (iteration 5): The previous errors were type mismatch errors when accessing `Vec<i32>` elements within `forall` and `exists` clauses. The fix was to cast `result[k as usize]` and `arr1[k as usize]` etc. to `int` when comparing them or assigning to a spec `int` variable. This ensures comparisons are done between `int` types, as array elements `i32` can be implicitly converted to `int` for these spec purposes. */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    let mut j = 0;

    while i < arr1.len() || j < arr2.len()
        invariant
            result.len() == (i + j),
            result.len() <= arr1.len() + arr2.len(),
            i <= arr1.len(),
            j <= arr2.len(),
            forall|k: int, l: int| 0 <= k < l < result.len() ==> (result[k as usize] as int) <= (result[l as usize] as int),
            forall|idx: int| 0 <= idx < i ==> (arr1[idx as usize] as int <= result.last().map(|x| *x as int).unwrap_or(i32::MIN as int)),
            forall|idx: int| 0 <= idx < j ==> (arr2[idx as usize] as int <= result.last().map(|x| *x as int).unwrap_or(i32::MIN as int)),
            forall|idx: int| 0 <= idx < result.len() ==> (
                (exists|k: int| 0 <= k < i && (result[idx as usize] as int) == (arr1[k as usize] as int)) ||
                (exists|k: int| 0 <= k < j && (result[idx as usize] as int) == (arr2[k as usize] as int))
            ),
        decreases (arr1.len() - i) + (arr2.len() - j),
    {
        if i < arr1.len() && (j >= arr2.len() || arr1[i] <= arr2[j]) {
            result.push(arr1[i]);
            i = i + 1;
        } else if j < arr2.len() && (i >= arr1.len() || arr2[j] < arr1[i]) {
            result.push(arr2[j]);
            j = j + 1;
        } else {
            proof { unreachable!(); }
        }
    }

    result
}
// </vc-code>

}
fn main() {}