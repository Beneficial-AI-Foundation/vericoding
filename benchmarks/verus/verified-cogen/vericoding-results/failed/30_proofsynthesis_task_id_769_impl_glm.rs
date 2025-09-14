// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added parentheses to while condition */
fn contains(v: &Vec<i32>, x: i32) -> (result: bool)
    ensures result == exists|i: int| 0 <= i < v.len() && v[i] == x
{
    let mut i = 0;
    while (i < v.len())
        invariant { 0 <= i <= v.len() }
        invariant { forall|j: int| 0 <= j < i ==> v[j] != x }
    {
        if v[i] == x {
            return true;
        }
        i += 1;
    }
    false
}
// </vc-helpers>

// <vc-spec>
fn difference(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)

    ensures
        forall|i: int|
            0 <= i < arr1.len() ==> (!arr2@.contains(#[trigger] arr1[i]) ==> result@.contains(
                arr1[i],
            )),
        forall|i: int|
            0 <= i < arr2.len() ==> (!arr1@.contains(#[trigger] arr2[i]) ==> result@.contains(
                arr2[i],
            )),
        forall|i: int, j: int|
            0 <= i < j < result.len() ==> #[trigger] result[i] != #[trigger] result[j],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added parentheses to while conditions */
{
    let mut result = Vec::new();
    let mut i = 0;
    while (i < arr1.len())
        invariant { 0 <= i <= arr1.len() }
        invariant { forall|k: int| 0 <= k < i ==> (!contains(arr2, arr1[k]) ==> contains(&result, arr1[k])) }
        invariant { forall|k: int| 0 <= k < result.len() ==> 
            exists|j: int| 0 <= j < i && arr1[j] == result[k] && !contains(arr2, arr1[j]) }
        invariant { forall|k: int, j: int| 0 <= k < j < result.len() ==> result[k] != result[j] }
    {
        let x = arr1[i];
        if !contains(arr2, x) {
            if !contains(&result, x) {
                result.push(x);
            }
        }
        i += 1;
    }
    let mut j = 0;
    while (j < arr2.len())
        invariant { 0 <= j <= arr2.len() }
        invariant { forall|k: int| 0 <= k < arr1.len() ==> (!contains(arr2, arr1[k]) ==> contains(&result, arr1[k])) }
        invariant { forall|k: int| 0 <= k < j ==> (!contains(arr1, arr2[k]) ==> contains(&result, arr2[k])) }
        invariant { forall|k: int| 0 <= k < result.len() ==> 
            (exists|idx: int| 0 <= idx < arr1.len() && arr1[idx] == result[k] && !contains(arr2, arr1[idx]))
            || (exists|idx: int| 0 <= idx < j && arr2[idx] == result[k] && !contains(arr1, arr2[idx])) }
        invariant { forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] != result[l] }
    {
        let x = arr2[j];
        if !contains(arr1, x) {
            if !contains(&result, x) {
                result.push(x);
            }
        }
        j += 1;
    }
    result
}
// </vc-code>

}
fn main() {}