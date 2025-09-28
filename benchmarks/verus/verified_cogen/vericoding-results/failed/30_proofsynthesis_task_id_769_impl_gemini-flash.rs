// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected parameter type for `contains` to match `Seq<i32>`. */
spec fn contains(s: Seq<i32>, elem: i32) -> bool {
    exists|i: int| #![auto]
        0 <= i < s.len() && s[i] == elem
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
/* code modified by LLM (iteration 5): Fixed compilation error in invariant syntax. */
{
    let mut result: Vec<i32> = Vec::new();
    let mut seen: Vec<i32> = Vec::new();

    let snk_arr1 = arr1.to_seq();
    let snk_arr2 = arr2.to_seq();

    let mut i = 0;
    while i < arr1.len()
        invariant 
            0 <= i <= arr1.len(),
            forall|j: int| 0 <= j < result.len() ==> (!snk_arr2.contains(result.view()[j]) || !snk_arr1.contains(result.view()[j])),
            forall|j: int| 0 <= j < result.len() ==> seen.view().contains(result.view()[j]),
            forall|j: int| 0 <= j < seen.len() ==> result.view().contains(seen.view()[j]),
            forall|a: int, b: int| 0 <= a < b < result.len() ==> result.view()[a] != result.view()[b],
            forall|k: int| 0 <= k < i ==> seen.view().contains(arr1.view()[k]),
            forall|k: int| 0 <= k < i && !snk_arr2.contains(arr1.view()[k]) ==> result.view().contains(arr1.view()[k]),
    {
        let val = arr1[i];
        if !snk_arr2.contains(val) && !seen.view().contains(val) {
            result.push(val);
            seen.push(val);
        }
        i = i + 1;
    }

    let mut i = 0;
    while i < arr2.len()
        invariant 
            0 <= i <= arr2.len(),
            forall|j: int| 0 <= j < result.len() ==> (!snk_arr2.contains(result.view()[j]) || !snk_arr1.contains(result.view()[j])),
            forall|j: int| 0 <= j < result.len() ==> seen.view().contains(result.view()[j]),
            forall|j: int| 0 <= j < seen.len() ==> result.view().contains(seen.view()[j]),
            forall|a: int, b: int| 0 <= a < b < result.len() ==> result.view()[a] != result.view()[b],
            forall|k: int| 0 <= k < arr1.len() ==> seen.view().contains(arr1.view()[k]),
            forall|k: int| 0 <= k < arr1.len() && !snk_arr2.contains(arr1.view()[k]) ==> result.view().contains(arr1.view()[k]),
            forall|k: int| 0 <= k < i ==> seen.view().contains(arr2.view()[k]),
            forall|k: int| 0 <= k < i && !snk_arr1.contains(arr2.view()[k]) ==> result.view().contains(arr2.view()[k]),
    {
        let val = arr2[i];
        if !snk_arr1.contains(val) && !seen.view().contains(val) {
            result.push(val);
            seen.push(val);
        }
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}