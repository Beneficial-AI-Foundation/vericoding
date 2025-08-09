use vstd::prelude::*;

verus! {

fn is_palindrome(text: &str) -> (result: bool)
    // post-conditions-start
    ensures
        result == forall|i: int|
            0 <= i < text@.len() ==> #[trigger] text@[i] == text@[text@.len() - 1 - i],
    // post-conditions-end
{
    /* code modified by LLM (iteration 1): replaced text.len() with text@.len() and fixed indexing to use sequence operations */
    let len = text@.len();
    let mut i: usize = 0;
    
    while i < len / 2
        invariant
            0 <= i <= len / 2,
            forall|j: int| 0 <= j < i ==> text@[j] == text@[len - 1 - j],
    {
        /* code modified by LLM (iteration 1): use sequence indexing with @ instead of as_bytes() */
        if text@[i as int] != text@[len - 1 - (i as int)] {
            return false;
        }
        i += 1;
    }
    
    true
}

}
fn main() {}