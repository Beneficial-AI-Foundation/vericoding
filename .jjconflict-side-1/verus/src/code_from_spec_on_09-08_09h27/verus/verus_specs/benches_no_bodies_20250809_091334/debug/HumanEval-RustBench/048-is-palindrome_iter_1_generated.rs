use vstd::prelude::*;

verus! {

fn is_palindrome(text: &str) -> (result: bool)
    // post-conditions-start
    ensures
        result == forall|i: int|
            0 <= i < text@.len() ==> #[trigger] text@[i] == text@[text@.len() - 1 - i],
    // post-conditions-end
{
    let len = text.len();
    let mut i = 0;
    
    while i < len / 2
        invariant
            0 <= i <= len / 2,
            forall|j: int| 0 <= j < i ==> text@[j] == text@[len - 1 - j],
    {
        if text.as_bytes()[i] != text.as_bytes()[len - 1 - i] {
            return false;
        }
        i += 1;
    }
    
    true
}

}
fn main() {}