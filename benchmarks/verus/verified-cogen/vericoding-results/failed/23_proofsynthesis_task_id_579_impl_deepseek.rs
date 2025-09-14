// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed Vec indexing using [] syntax instead of index() method */
fn is_in(x: i32, arr: Seq<i32>) -> bool {
    exists|i: int| 0 <= i < arr.len() && arr[i] == x
}

proof fn distinct_lemma(result: Seq<i32>, i: int, j: int)
    requires
        0 <= i < j < result.len(),
    ensures
        result[i] != result[j]
{
}

proof fn result_contains_arr1_lemma(arr1: Seq<i32>, arr2: Seq<i32>, result: Seq<i32>, i: int)
    requires
        0 <= i < arr1.len(),
        !is_in(arr1[i], arr2),
    ensures
        is_in(arr1[i], result)
{
}

proof fn result_contains_arr2_lemma(arr1: Seq<i32>, arr2: Seq<i32>, result: Seq<i32>, i: int)
    requires
        0 <= i < arr2.len(),
        !is_in(arr2[i], arr1),
    ensures
        is_in(arr2[i], result)
{
}
// </vc-helpers>

// <vc-spec>
fn find_dissimilar(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)

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
/* code modified by LLM (iteration 5): Fixed Vec indexing using [] syntax instead of index() method */
{
    let mut result = Vec::new();
    
    let mut seen = Vec::new();
    
    let mut i = 0;
    while i < arr1.len()
        invariant
            i <= arr1.len(),
            forall|k: int| 0 <= k < arr1.len() ==> (!is_in(arr1[k], arr2@) ==> is_in(arr1[k], result@)),
            forall|k: int| 0 <= k < arr2.len() ==> (!is_in(arr2[k], arr1@) ==> is_in(arr2[k], result@)),
            forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] != result[l],
    {
        let elem = arr1[i];
        if !is_in(elem, arr2@) && !is_in(elem, seen@) {
            result.push(elem);
            seen.push(elem);
        }
        i += 1;
    }
    
    let mut j = 0;
    while j < arr2.len()
        invariant
            j <= arr2.len(),
            forall|k: int| 0 <= k < arr1.len() ==> (!is_in(arr1[k], arr2@) ==> is_in(arr1[k], result@)),
            forall|k: int| 0 <= k < arr2.len() ==> (!is_in(arr2[k], arr1@) ==> is_in(arr2[k], result@)),
            forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] != result[l],
    {
        let elem = arr2[j];
        if !is_in(elem, arr1@) && !is_in(elem, seen@) {
            result.push(elem);
            seen.push(elem);
        }
        j += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}