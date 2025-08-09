use vstd::prelude::*;

verus! {

fn is_palindrome(text: &str) -> (result: bool)
    // post-conditions-start
    ensures
        result == forall|i: int|
            0 <= i < text@.len() ==> #[trigger] text@[i] == text@[text@.len() - 1 - i],
    // post-conditions-end
{
    /* code modified by LLM (iteration 4): work directly with string sequence instead of chars().collect() */
    let len = text.len();
    let mut i: usize = 0;
    
    while i < len / 2
        invariant
            0 <= i <= len / 2,
            forall|j: int| 0 <= j < i ==> text@[j] == text@[text@.len() - 1 - j],
    {
        /* code modified by LLM (iteration 4): access string bytes directly using as_bytes() */
        if text.as_bytes()[i] != text.as_bytes()[len - 1 - i] {
            return false;
        }
        i += 1;
    }
    
    true
}

}
fn main() {}