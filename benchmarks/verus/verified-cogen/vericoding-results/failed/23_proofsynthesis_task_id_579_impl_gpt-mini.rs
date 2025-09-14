// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): define vec_contains for Vec<i32> using exists */
spec fn vec_contains(v: &Vec<i32>, x: i32) -> bool { exists |i: int| 0 <= i < v.len() as int && v@[i] == x }
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
{
    /* code modified by LLM (iteration 5): build result without duplicates from arr1 and arr2 using vec_contains helper, using usize indices to avoid ghost int in loops */
    let mut result: Vec<i32> = Vec::new();

    let mut i: usize = 0;
    while i < arr1.len()
        invariant
            i <= arr1.len(),
            forall|k: int| 0 <= k < i as int ==> (!vec_contains(arr2, arr1@[k]) ==> vec_contains(&result, arr1@[k])),
            forall|p: int, q: int| 0 <= p < q < result.len() as int ==> result@[p] != result@[q],
        decreases
            arr1.len() - i
    {
        let v = arr1[i];
        if !vec_contains(arr2, v) && !vec_contains(&result, v) {
            proof {
                assert(!vec_contains(&result, v));
                assert(forall|p: int| 0 <= p < result.len() as int ==> result@[p] != v);
                assert(forall|p: int, q: int| 0 <= p < q < result.len() as int ==> result@[p] != result@[q]);
                assert(forall|p: int, q: int| 0 <= p < q < result.len() as int + 1 ==> result@[p] != result@[q]);
            }
            result.push(v);
        }
        i = i + 1;
    }

    let mut j: usize = 0;
    while j < arr2.len()
        invariant
            j <= arr2.len(),
            forall|k: int| 0 <= k < j as int ==> (!vec_contains(arr1, arr2@[k]) ==> vec_contains(&result, arr2@[k])),
            forall|p: int, q: int| 0 <= p < q < result.len() as int ==> result@[p] != result@[q],
        decreases
            arr2.len() - j
    {
        let v = arr2[j];
        if !vec_contains(arr1, v) && !vec_contains(&result, v) {
            proof {
                assert(!vec_contains(&result, v));
                assert(forall|p: int| 0 <= p < result.len() as int ==> result@[p] != v);
                assert(forall|p: int, q: int| 0 <= p < q < result.len() as int ==> result@[p] != result@[q]);
                assert(forall|p: int, q: int| 0 <= p < q < result.len() as int + 1 ==> result@[p] != result@[q]);
            }
            result.push(v);
        }
        j = j + 1;
    }

    result
}

// </vc-code>

}
fn main() {}