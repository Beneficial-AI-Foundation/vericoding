// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes needed in this iteration. */
fn double_element(x: i32) -> i32 { x * 2 }
// </vc-helpers>

// <vc-spec>
fn double_array_elements(s: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> #[trigger] result[i] == 2 * s[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Cast loop variables to usize for comparison and indexing, and ensure proper types for array operations, fixing errors with indexing `s` with `int` type. */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let s_len: usize = s.len();
    while i < s_len
        invariant
            result.len() == i,
            s.len() == s_len,
            forall|j: int| 0 <= j && (j as usize) < i ==> #[trigger] result[j as usize] == 2 * s[j as usize],
        decreases s_len - i,
    {
        result.push(double_element(s[i]));
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}