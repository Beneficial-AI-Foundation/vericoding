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
    let bytes = text.as_bytes();
    let len_bytes = bytes.len();
    let mut i: usize = 0;
    while i < len_bytes / 2
        invariant
            0 <= i <= (len_bytes as int) / 2,
            forall|j: int| 0 <= j < i ==> #[trigger] bytes@[j as int] == bytes@[(len_bytes as int) - 1 - j],
    {
        if bytes@[i as int] != bytes@[(len_bytes as int) - 1 - (i as int)] {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

fn main() {}
}