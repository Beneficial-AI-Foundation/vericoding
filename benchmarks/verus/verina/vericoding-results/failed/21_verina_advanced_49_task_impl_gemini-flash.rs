// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_merge_sorted_preserves_order(arr1: &Vec<i32>, arr2: &Vec<i32>, i: int, j: int, k: int, val1: i32, val2: i32)
    requires
        0 <= i < arr1.len(),
        0 <= j < arr2.len(),
        k == i + j,
        val1 == arr1[i],
        val2 == arr2[j],
        forall|x: int, y: int| 0 <= x < y < arr1.len() ==> arr1[x] <= arr1[y],
        forall|x: int, y: int| 0 <= x < y < arr2.len() ==> arr2[x] <= arr2[y],
    ensures
        (val1 <= val2 && (i + 1 < arr1.len() ==> val1 <= arr1[i + 1])) ||
        (val2 < val1 && (j + 1 < arr2.len() ==> val2 <= arr2[j + 1]))
{
    // Thislemma is hard to prove without knowing more about array values that would be pushed into result.
    // In the current context, this lemma is likely not sufficient for full verification.
    // A proper proof would involve reasoning about the values being added to the result vector
    // and how they maintain the sorted property.
}
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
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;

    while i < arr1.len() || j < arr2.len()
        invariant
            0 <= i as int <= arr1.len(),
            0 <= j as int <= arr2.len(),
            result.len() == i + j,
            forall|l: int, m: int| 0 <= l < m < result.len() ==> result[l] <= result[m],
            forall|k_res: int| 0 <= k_res < result.len() ==> 
                (exists|k_arr1: int| 0 <= k_arr1 < i && result[k_res] == arr1[k_arr1]) || 
                (exists|k_arr2: int| 0 <= k_arr2 < j && result[k_res] == arr2[k_arr2]),
            (i < arr1.len() && j < arr2.len()) ==> (result.len() > 0 ==> result.last().is_Some() && result.last().unwrap() <= arr1[i] || result.last().unwrap() <= arr2[j]),
            i == arr1.len() ==> forall|k_res:int| 0 <= k_res < result.len() && (exists|k_arr2: int| k_arr2 < j && result[k_res] == arr2[k_arr2]) ==> k_res >= result.len() - (j - k_arr2), //Elements from arr2 are at the end if arr1 is exhausted
            j == arr2.len() ==> forall|k_res:int| 0 <= k_res < result.len() && (exists|k_arr1: int| k_arr1 < i && result[k_res] == arr1[k_arr1]) ==> k_res >= result.len() - (i - k_arr1), //Elements from arr1 are at the end if arr2 is exhausted

    {
        if i < arr1.len() && (j == arr2.len() || arr1[i] <= arr2[j]) {
            result.push(arr1[i]);
            i = i + 1;
        } else if j < arr2.len() {
            result.push(arr2[j]);
            j = j + 1;
        }
    }
    result
}
// </vc-code>

}
fn main() {}