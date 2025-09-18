// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected `all_chars_digit` definition to follow `spec fn` syntax properly. */
spec fn all_chars_digit(s: Seq<char>) -> bool { forall|i: int| 0 <= i < s.len() ==> '0' <= s[i] <= '9' }
// </vc-helpers>

// <vc-spec>
spec fn all_chars_digit(s: Seq<char>) -> bool;

fn isdigit(a: Vec<String>) -> (result: Vec<bool>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == (a[i]@.len() > 0 && all_chars_digit(a[i]@))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Simplified `isdigit` implementation logic. */
{
    let mut result = Vec::with_capacity(a.len() as usize);
    let mut i: int = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (a[j]@.len() > 0 && all_chars_digit(a[j]@))
    {
        let s = a[i]@;
        let current_is_digit = s.len() > 0 && all_chars_digit(s);
        result.push(current_is_digit);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}