// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_even(n: i32) -> bool {
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): trivial helper preserved for extensibility */
spec fn helper_true() -> bool { true }
// </vc-helpers>

// <vc-spec>
fn find_even_numbers(arr: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|i: int| 0 <= i < result.len() ==> is_even(#[trigger] result[i]),
        forall|i: int| 0 <= i < result.len() ==> exists|j: int| 0 <= j < arr.len() && #[trigger] result[i] == arr[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): collect even elements using usize indices */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            forall|k: usize| k < result.len() ==> exists|j: usize| j < arr.len() && result[k] == arr[j] && is_even(result[k]),
        decreases arr.len() - i
    {
        let ai: i32 = arr[i];
        if is_even(ai) {
            let old_len: usize = result.len();
            assert(forall|k: usize| k < old_len ==> exists|j: usize| j < arr.len() && result[k] == arr[j] && is_even(result[k]));
            result.push(ai);
            proof {
                assert(result[old_len] == ai);
                assert(ai == arr[i]);
                assert(is_even(ai));
                assert(exists|j: usize| j < arr.len() && result[old_len] == arr[j] && is_even(result[old_len]));
                assert(forall|k: usize| k < result.len() ==> exists|j: usize| j < arr.len() && result[k] == arr[j] && is_even(result[k]));
            }
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}