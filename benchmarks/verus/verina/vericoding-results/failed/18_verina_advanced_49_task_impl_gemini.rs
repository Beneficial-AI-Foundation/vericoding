// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): defined is_sorted spec function to fix compilation error */
spec fn is_sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
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
    /* code modified by LLM (iteration 2): re-submitting code to check verification after fixing compilation error */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;

    while i < arr1.len() && j < arr2.len()
        invariant
            0 <= i <= arr1.len(),
            0 <= j <= arr2.len(),
            result.len() == i + j,
            is_sorted(result.view()),
            forall|k: int, l: int| (0 <= k < result.len() && i <= l < arr1.len()) ==> result.view()[k] <= arr1.view()[l],
            forall|k: int, l: int| (0 <= k < result.len() && j <= l < arr2.len()) ==> result.view()[k] <= arr2.view()[l],
        decreases (arr1.len() - i) + (arr2.len() - j)
    {
        if arr1[i] <= arr2[j] {
            result.push(arr1[i]);
            i = i + 1;
        } else {
            result.push(arr2[j]);
            j = j + 1;
        }
    }

    while i < arr1.len()
        invariant
            j == arr2.len(),
            0 <= i <= arr1.len(),
            result.len() == i + j,
            is_sorted(result.view()),
            forall|k: int, l: int| (0 <= k < result.len() && i <= l < arr1.len()) ==> result.view()[k] <= arr1.view()[l],
        decreases arr1.len() - i
    {
        result.push(arr1[i]);
        i = i + 1;
    }

    while j < arr2.len()
        invariant
            i == arr1.len(),
            0 <= j <= arr2.len(),
            result.len() == i + j,
            is_sorted(result.view()),
            forall|k: int, l: int| (0 <= k < result.len() && j <= l < arr2.len()) ==> result.view()[k] <= arr2.view()[l],
        decreases arr2.len() - j
    {
        result.push(arr2[j]);
        j = j + 1;
    }

    result
}
// </vc-code>

}
fn main() {}