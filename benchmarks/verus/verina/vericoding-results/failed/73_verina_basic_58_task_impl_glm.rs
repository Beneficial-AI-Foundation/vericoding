// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn double_array_elements(s: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> #[trigger] result[i] == 2 * s[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added trigger to quantifier in loop invariant */
    let mut result = Vec::with_capacity(s.len());
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == 2 * s[j],
        decreases s.len() - i,
    {
        result.push(2 * s[i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}