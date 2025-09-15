// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): pure helper to double an i32 */
fn twice(x: i32) -> i32 { 2 * x }
// </vc-helpers>

// <vc-spec>
fn double_array_elements(s: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> #[trigger] result[i] == 2 * s[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): construct result Vec by pushing doubled elements with loop and invariants */
    let mut result: Vec<i32> = Vec::new();
    let mut i: int = 0;
    while i < s.len()
        invariant { result.len() == i },
        invariant { forall|k: int| 0 <= k < i ==> result[k] == 2 * s[k] },
        decreases s.len() - i
    {
        let v: i32 = twice(s[i]);
        result.push(v);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}