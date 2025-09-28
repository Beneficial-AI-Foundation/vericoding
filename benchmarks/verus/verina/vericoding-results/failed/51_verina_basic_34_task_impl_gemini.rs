// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_even(n: i32) -> bool {
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers needed */
// </vc-helpers>

// <vc-spec>
fn find_even_numbers(arr: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|x: i32| result@.contains(x) ==> is_even(x) && arr@.contains(x),
        forall|x: i32| arr@.contains(x) && is_even(x) ==> result@.contains(x),
        forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() && i <= j && 
            is_even(arr[i]) && is_even(arr[j]) ==> {
                exists|ri: int, rj: int| 0 <= ri < result.len() && 0 <= rj < result.len() && 
                    ri <= rj && result[ri] == arr[i] && result[rj] == arr[j]
            },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed incorrect lemma names based on compiler errors */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|x: i32| #[trigger] result@.contains(x) ==> is_even(x) && arr@.subrange(0, i as int).contains(x),
            forall|k: int| 0 <= k < (i as int) && is_even(arr@[k]) ==> result@.contains(arr@[k]),
            forall|j1: int, j2: int|
                0 <= j1 < (i as int) && 0 <= j2 < (i as int) && j1 <= j2 &&
                is_even(arr@[j1]) && is_even(arr@[j2]) ==> 
                (exists|r1: int, r2: int| 
                    0 <= r1 < result.len() && 0 <= r2 < result.len() && r1 <= r2 &&
                    result@[r1] == arr@[j1] && result@[r2] == arr@[j2]),
        decreases arr.len() - i
    {
        let item = arr[i];
        if item % 2 == 0 {
            proof { assert(is_even(item)); }
            let ghost result_old = result@;
            result.push(item);
            proof {
                // The previous attempt used non-existent lemmas from `vstd::seq`.
                // `lemma_push_is_append_singleton` is not needed as `push` is definitional.
                // `lemma_subrange_of_push` is replaced by `lemma_subrange_of_add` from `vstd::seq_lib`.
                vstd::seq_lib::lemma_append_last(result_old, seq![item]);
                vstd::seq_lib::lemma_subrange_of_add(result_old, seq![item]);
            }
        } else {
            proof { assert(!is_even(item)); }
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}