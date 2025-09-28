// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn contains_value(arr: Seq<i32>, val: i32) -> bool {
    exists|i: int| 0 <= i < arr.len() && arr[i] == val
}

/* helper modified by LLM (iteration 5): Added spec function for sequence contains check */
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
{
    /* code modified by LLM (iteration 5): Fixed type errors by using usize for indexing */
    let mut result = Vec::new();
    let ghost mut seen = Set::<i32>::empty();
    
    let mut i: usize = 0;
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            forall|j: int| 0 <= j < i as int && !arr2@.contains(arr1[j]) && !seen.contains(arr1[j]) ==> result@.contains(arr1[j]),
            forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] != result[l],
            forall|j: int| 0 <= j < result.len() ==> seen.contains(result[j]),
    {
        if !arr2@.contains(arr1[i as int]) {
            let mut already_added = false;
            let mut j: usize = 0;
            while j < result.len()
                invariant
                    0 <= j <= result.len(),
                    already_added == exists|k: int| 0 <= k < j as int && result[k] == arr1[i as int],
            {
                if result[j as int] == arr1[i as int] {
                    already_added = true;
                }
                j = j + 1;
            }
            if !already_added {
                proof {
                    seen = seen.insert(arr1[i as int]);
                }
                result.push(arr1[i as int]);
            }
        }
        i = i + 1;
    }
    
    let mut i: usize = 0;
    while i < arr2.len()
        invariant
            0 <= i <= arr2.len(),
            forall|j: int| 0 <= j < arr1.len() && !arr2@.contains(arr1[j]) && !seen.contains(arr1[j]) ==> result@.contains(arr1[j]),
            forall|j: int| 0 <= j < i as int && !arr1@.contains(arr2[j]) && !seen.contains(arr2[j]) ==> result@.contains(arr2[j]),
            forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] != result[l],
            forall|j: int| 0 <= j < result.len() ==> seen.contains(result[j]),
    {
        if !arr1@.contains(arr2[i as int]) {
            let mut already_added = false;
            let mut j: usize = 0;
            while j < result.len()
                invariant
                    0 <= j <= result.len(),
                    already_added == exists|k: int| 0 <= k < j as int && result[k] == arr2[i as int],
            {
                if result[j as int] == arr2[i as int] {
                    already_added = true;
                }
                j = j + 1;
            }
            if !already_added {
                proof {
                    seen = seen.insert(arr2[i as int]);
                }
                result.push(arr2[i as int]);
            }
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}