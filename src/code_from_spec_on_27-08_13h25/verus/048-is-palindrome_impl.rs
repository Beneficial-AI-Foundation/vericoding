use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers in this case
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
fn is_palindrome(text: &str) -> (result: bool)
    ensures
        result == forall|i: int|
            0 <= i < text@.len() ==> #[trigger] text@[i] == text@[text@.len() - 1 - i],
{
    let len = text@.len();
    if len == 0 {
        return true;
    }
    let mut i: usize = 0;
    while i < len / 2
        invariant
            len == text@.len(),
            i <= len / 2,
            forall|j: int| 0 <= j < i ==> #[trigger] text@[j] == text@[len - 1 - j],
    {
        if text@[i] != text@[len - 1 - i] {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}