// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_even(n: i32) -> bool {
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [no helpers provided - this section is empty] */
// </vc-helpers>

// <vc-spec>
fn find_even_numbers(arr: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|i: int| 0 <= i < result.len() ==> is_even(#[trigger] result[i]),
        forall|i: int| 0 <= i < result.len() ==> exists|j: int| 0 <= j < arr.len() && #[trigger] result[i] == arr[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [removed `code` from `code is_even` resulting in valid call to `is_even`] */
    let mut result_vec: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    while i < arr.len()
        invariant
            0 <= i && i <= arr.len(),
            forall|k: int| 0 <= k < result_vec.len() ==> is_even(#[trigger] result_vec[k]),
            forall|k: int| 0 <= k < result_vec.len() ==> exists|j: int| 0 <= j < i as int && #[trigger] result_vec[k] == arr@[j as int]
        decreases arr.len() - i
    {
        let current_val = arr[i];
        if (is_even(current_val)) {
            result_vec.push(current_val);
        }
        i = i + 1;
    }

    result_vec
}
// </vc-code>

}
fn main() {}