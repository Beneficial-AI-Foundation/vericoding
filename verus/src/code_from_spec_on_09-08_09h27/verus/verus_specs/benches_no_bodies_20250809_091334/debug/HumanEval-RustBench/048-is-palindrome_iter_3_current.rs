use vstd::prelude::*;

verus! {

fn is_palindrome(text: &str) -> (result: bool)
    // post-conditions-start
    ensures
        result == forall|i: int|
            0 <= i < text@.len() ==> #[trigger] text@[i] == text@[text@.len() - 1 - i],
    // post-conditions-end
{
    /* code modified by LLM (iteration 2): use as_bytes() for executable code while maintaining ghost reasoning with @ */
    let bytes = text.as_bytes();
    let len = bytes.len();
    let mut i: usize = 0;
    
    while i < len / 2
        invariant
            0 <= i <= len / 2,
            bytes@ == text@,
            forall|j: int| 0 <= j < i ==> text@[j] == text@[text@.len() - 1 - j],
    {
        /* code modified by LLM (iteration 2): compare bytes directly in executable code */
        if bytes[i] != bytes[len - 1 - i] {
            return false;
        }
        i += 1;
    }
    
    true
}

}
fn main() {}