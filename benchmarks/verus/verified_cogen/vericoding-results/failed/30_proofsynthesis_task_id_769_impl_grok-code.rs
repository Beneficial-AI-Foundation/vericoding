// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
/* code modified by LLM (iteration 5): fixed loop invariants to properly track added elements from arr1 and arr2 without assuming uniqueness in arrays */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            forall |j: int| 0 <= j < i ==> (!arr2@.contains(#[trigger] arr1@[j]) ==> result@.contains(arr1@[j])),
            forall |k: int, l: int| 0 <= k < l < result.len() ==> result@[k] != result@[l]
        decreases arr1.len() - i
    {
        let elem = arr1[i];
        if !arr2@.contains(elem) && !result@.contains(elem) {
            result.push(elem);
        }
        i += 1;
    }
    let mut j = 0;
    while j < arr2.len()
        invariant
            0 <= j <= arr2.len(),
            i == arr1.len(),
            forall |p: int| 0 <= p < i ==> (!arr2@.contains(#[trigger] arr1@[p]) ==> result@.contains(arr1@[p])),
            forall |m: int| 0 <= m < j ==> (!arr1@.contains(#[trigger] arr2@[m]) ==> result@.contains(arr2@[m])),
            forall |k: int, l: int| 0 <= k < l < result.len() ==> result@[k] != result@[l]
        decreases arr2.len() - j
    {
        let elem = arr2[j];
        if !arr1@.contains(elem) && !result@.contains(elem) {
            result.push(elem);
        }
        j += 1;
    }
    result
}
// </vc-code>

}
fn main() {}