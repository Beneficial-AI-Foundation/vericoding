// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): removed duplicate all_chars_digit */
// </vc-helpers>

// <vc-spec>
spec fn all_chars_digit(s: Seq<char>) -> bool;

fn isdigit(a: Vec<String>) -> (result: Vec<bool>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == (a[i]@.len() > 0 && all_chars_digit(a[i]@))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): removed proof block that relied on all_chars_digit body */
{
    let mut result = Vec::new();
    for i in 0..a.len() {
        let s = a[i].as_str();
        let all_digit = s.len() > 0 && s.chars().all(|c| '0' <= c && c <= '9');
        result.push(all_digit);
    }
    result
}
// </vc-code>

}
fn main() {}