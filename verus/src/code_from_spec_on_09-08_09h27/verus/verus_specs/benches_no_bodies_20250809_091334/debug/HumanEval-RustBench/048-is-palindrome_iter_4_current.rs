use vstd::prelude::*;

verus! {

fn is_palindrome(text: &str) -> (result: bool)
    // post-conditions-start
    ensures
        result == forall|i: int|
            0 <= i < text@.len() ==> #[trigger] text@[i] == text@[text@.len() - 1 - i],
    // post-conditions-end
{
    /* code modified by LLM (iteration 3): remove invalid bytes@ == text@ invariant and use chars for comparison */
    let chars: Vec<char> = text.chars().collect();
    let len = chars.len();
    let mut i: usize = 0;
    
    while i < len / 2
        invariant
            0 <= i <= len / 2,
            chars@ == text@,
            forall|j: int| 0 <= j < i ==> text@[j] == text@[text@.len() - 1 - j],
    {
        /* code modified by LLM (iteration 3): compare chars instead of bytes */
        if chars[i] != chars[len - 1 - i] {
            return false;
        }
        i += 1;
    }
    
    true
}

}
fn main() {}