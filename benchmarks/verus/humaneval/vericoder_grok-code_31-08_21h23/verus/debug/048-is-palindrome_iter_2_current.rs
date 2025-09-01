use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let chars: Vec<char> = text.chars().collect();
    let len = chars.len();
    let mut i: usize = 0;
    while i < len / 2
        invariant
            0 <= i <= (len as int) / 2,
            forall|j: int| 0 <= j < (i as int) ==> #[trigger] chars@[j] == chars@[(len as int) - 1 - j],
    {
        if chars[i] != chars[len - 1 - i] {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

fn main() {}
}