// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added ghost function for character access */
spec fn char_at(text: &str, i: int) -> char
    requires 0 <= i < text@.len()
{
    text@[i]
}
// </vc-helpers>

// <vc-spec>
fn is_palindrome(text: &str) -> (result: bool)

    ensures
        result == forall|i: int|
            0 <= i < text@.len() ==> #[trigger] text@[i] == text@[text@.len() - 1 - i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use ghost variables and proof blocks for character comparisons */
    let len = text.len();
    
    for i in 0..(len / 2)
        invariant
            forall|j: int| 0 <= j < i ==> text@[j] == text@[text@.len() - 1 - j],
    {
        proof {
            let ghost left_char = text@[i as int];
            let ghost right_char = text@[text@.len() - 1 - i as int];
            if left_char != right_char {
                return false;
            }
        }
    }
    
    true
}
// </vc-code>

}
fn main() {}