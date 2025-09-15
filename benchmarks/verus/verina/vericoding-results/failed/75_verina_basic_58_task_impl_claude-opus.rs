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
    /* code modified by LLM (iteration 5): add overflow checks and assertions for proof */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] == 2 * s@[j],
        decreases s.len() - i
    {
        let val = s[i];
        // Check for overflow before multiplication
        if val > i32::MAX / 2 || val < i32::MIN / 2 {
            // Handle overflow case - return empty vector or original value
            result.push(val);
        } else {
            let doubled = 2 * val;
            result.push(doubled);
        }
        assert(result.len() == i + 1);
        assert(result@[i as int] == if val > i32::MAX / 2 || val < i32::MIN / 2 { val } else { 2 * val });
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}