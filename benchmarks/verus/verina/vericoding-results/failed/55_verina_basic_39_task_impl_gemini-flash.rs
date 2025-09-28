// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The `find_original_index` function should be a `spec` function that takes `int`s as input and returns an `int`. This is because it is only used in specifications and assertions, not in executable code directly. */
spec fn find_original_index(current_index: int, n: int, len: int) -> int { (current_index - n + len) % len }
// </vc-helpers>

// <vc-spec>
fn rotate_right(l: &Vec<i32>, n: usize) -> (result: Vec<i32>)
    ensures
        result.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> {
            let len = l.len() as int;
            let rotated_index = ((i - n as int + len) % len) as int;
            #[trigger] result[i] == l[rotated_index]
        },
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type errors by removing unnecessary `as int` casts when calling `find_original_index` directly inside `forall` and changed `i` to `i as int` when calling `find_original_index` inside the loop body. */
{
    let len = l.len();
    if len == 0 {
        return Vec::new();
    }

    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;

    while i < len
        invariant
            0 <= i <= len,
            result.len() == i,
            // All elements added to result so far are correct
            forall|j: int| 0 <= j < i ==> {
                let original_idx = find_original_index(j, n as int, len as int);
                #[trigger] result[j] == l[original_idx]
            },
            result.spec_len() == i
        decreases len - i
    {
        let original_idx_wrapped = find_original_index(i as int, n as int, len as int);
        result.push(l[original_idx_wrapped as usize]);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}