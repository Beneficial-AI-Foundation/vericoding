//IMPL is_palindrome
use vstd::prelude::*;

verus! {

fn is_palindrome(text: &str) -> (result: bool)
    /* code modified by LLM (iteration 1): Moved ensures clause to correct position before function body */
    ensures
        result == forall|i: int|
            0 <= i < text@.len() ==> #[trigger] text@[i] == text@[text@.len() - 1 - i],
{
    /* code modified by LLM (iteration 1): Implemented palindrome check with proper loop invariants */
    let len = text.len();
    if len == 0 {
        return true;
    }
    
    let mut left = 0;
    let mut right = len - 1;
    
    while left < right
        invariant
            0 <= left <= len,
            0 <= right < len,
            left + right + 1 == len,
            forall|i: int| 0 <= i < left ==> text@[i] == text@[len - 1 - i],
    {
        if text.as_bytes()[left] != text.as_bytes()[right] {
            return false;
        }
        left += 1;
        right -= 1;
    }
    
    true
}

}
fn main() {}