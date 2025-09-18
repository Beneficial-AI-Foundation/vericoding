// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn unique(arr: Vec<i32>) -> (result: Vec<i32>)
    ensures

        forall|i: int, j: int| #![trigger result[i], result[j]] 0 <= i < j < result.len() ==> result[i] < result[j],

        forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==> exists|j: int| 0 <= j < arr.len() && result[i] == arr[j],

        forall|i: int, j: int| #![trigger result[i], result[j]] 0 <= i < result.len() && 0 <= j < result.len() && i != j ==> result[i] != result[j],

        forall|i: int| #![trigger arr[i]] 0 <= i < arr.len() ==> exists|j: int| 0 <= j < result.len() && arr[i] == result[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation errors by using correct functions from vstd (sort_vec, lemma_permutation_to_set_is_equal). */
    let ghost original_arr_seq = arr@;
    let mut sorted_arr = arr;
    vstd::vec::sort_vec(&mut sorted_arr);

    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < sorted_arr.len()
        invariant
            sorted_arr@.is_permutation(original_arr_seq),
            forall|k, l| 0 <= k < l < sorted_arr.len() ==> sorted_arr@[k] <= sorted_arr@[l],
            forall|k, l| 0 <= k < l < result.len() ==> result@[k] < result@[l],
            result@.to_set() == sorted_arr@.subrange(0, i as int).to_set(),
        decreases sorted_arr.len() - i
    {
        if i == 0 || sorted_arr[i] != sorted_arr[i-1] {
            result.push(sorted_arr[i]);
        }
        i = i + 1;
    }

    proof {
        vstd::seq_lib::lemma_permutation_to_set_is_equal(original_arr_seq, sorted_arr@);
    }
    result
}
// </vc-code>

}
fn main() {}