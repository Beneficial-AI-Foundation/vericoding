use vstd::prelude::*;

verus! {

fn is_palindrome(text: &str) -> (result: bool)
    // post-conditions-start
    ensures
        result == forall|i: int|
            0 <= i < text@.len() ==> #[trigger] text@[i] == text@[text@.len() - 1 - i],
    // post-conditions-end
{
    let len = text.unicode_len();
    
    if len == 0 {
        return true;
    }
    
    let mut j = 0;
    
    while j < len / 2
        invariant
            0 <= j <= len / 2,
            forall|k: int| 0 <= k < j ==> #[trigger] text@[k] == text@[len - 1 - k],
    {
        if text.get_char(j) != text.get_char(len - 1 - j) {
            return false;
        }
        j += 1;
    }
    
    true
}

}
fn main() {}