// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_even(n: i32) -> bool {
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The `is_even` helper function is already defined in the preamble, so this section is intentionally left empty. */
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
/* code modified by LLM (iteration 5): Adjusted the 'is_even' call to pass 'arr[i]' directly, as 'is_even' expects an 'i32' type, not 'int'. The `as int` cast was incorrect. */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i,
            i <= arr.len(),
            forall|j: int| 0 <= j < i ==> {
                !is_even(arr[j]) ==> !result@.contains(arr[j])
            },
            forall|j: int| 0 <= j < i ==> {
                is_even(arr[j]) ==> result@.contains(arr[j])
            },
            forall|v: i32| result@.contains(v) ==> {
                exists|k: int| 0 <= k < i && arr[k] == v && is_even(arr[k])
            },
        decreases arr.len() - i
    {
        if is_even(arr[i]) {
            result.push(arr[i]);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}