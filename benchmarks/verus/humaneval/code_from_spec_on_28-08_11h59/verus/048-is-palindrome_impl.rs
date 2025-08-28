use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn is_valid_palindrome(text: &str) -> bool {
    forall|i: int|
        0 <= i < text@.len() ==> #[trigger] text@[i] == text@[text@.len() - 1 - i]
}
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
    let len = text@.len();
    
    if len == 0 {
        return true;
    }
    
    let mut i = 0nat;
    while i < len / 2
        invariant
            0 <= i <= len / 2,
            forall|j: int| 0 <= j < i ==> text@[j] == text@[len - 1 - j],
    {
        if text.as_bytes()[i as usize] != text.as_bytes()[(len - 1 - i) as usize] {
            return false;
        }
        i += 1;
    }
    
    true
}
// </vc-code>

}
fn main() {}