// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers needed. */
// </vc-helpers>

// <vc-spec>
fn double_array_elements(s: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> #[trigger] result[i] == 2 * s[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed arithmetic overflow/underflow and loop invariant for `Vec<i32>` elements. */
{
    let mut result = Vec::new();
    result.reserve(s.len());
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i as int && i as int <= s.len() as int,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> #[trigger] result@[j] == (2 * (s@[j] as int)) as i32, // Cast to int for multiplication then back to i32
        decreases s.len() - i
    {
        // Explicitly cast to int for multiplication to avoid overflow, then cast back to i32.
        result.push((2 * (s[i] as int)) as i32);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}