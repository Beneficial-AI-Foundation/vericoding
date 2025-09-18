// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): checks all chars in sequence are digits */
spec fn all_chars_digit(s: Seq<char>) -> bool { forall|i: int| 0 <= i < s.len() ==> '0' <= s@[i] && s@[i] <= '9' }
// </vc-helpers>

// <vc-spec>
spec fn all_chars_digit(s: Seq<char>) -> bool;

fn isdigit(a: Vec<String>) -> (result: Vec<bool>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == (a[i]@.len() > 0 && all_chars_digit(a[i]@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement loop computing boolean vector with invariants */
    let mut result: Vec<bool> = Vec::<bool>::new();
    let mut i: int = 0;
    while i < a.len()
        invariant 0 <= i && i <= a.len()
        invariant result.len() == i
        invariant forall|j: int| 0 <= j < i ==> result[j] == (a[j]@.len() > 0 && all_chars_digit(a[j]@))
        decreases a.len() - i
    {
        let s: Seq<char> = a[i]@;
        let b: bool = s.len() > 0 && all_chars_digit(s);
        result.push(b);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}