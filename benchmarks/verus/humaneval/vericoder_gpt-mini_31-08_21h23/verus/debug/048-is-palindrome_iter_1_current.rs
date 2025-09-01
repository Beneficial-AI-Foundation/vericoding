use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
fn is_palindrome(text: &str) -> (result: bool)
    // post-conditions-start
    ensures
        result == forall|i: int|
            0 <= i < text@.len() ==> #[trigger] text@[i] == text@[text@.len() - 1 - i],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    forall|i: int| 0 <= i < text@.len() ==> #[trigger] text@[i] == text@[text@.len() - 1 - i]
}
// </vc-code>

fn main() {}
}