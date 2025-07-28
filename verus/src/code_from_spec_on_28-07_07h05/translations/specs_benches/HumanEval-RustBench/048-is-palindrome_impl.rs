use vstd::prelude::*;

verus! {

fn is_palindrome(text: &str) -> (result: bool)
    // post-conditions-start
    ensures
        result == forall|i: int|
            0 <= i < text@.len() ==> #[trigger] text@[i] == text@[text@.len() - 1 - i],
    // post-conditions-end
{
    /* code modified by LLM (iteration 4): Convert string to bytes for executable indexing */
    let text_bytes = text.as_bytes();
    let len = text_bytes.len();
    let mut i: usize = 0;
    
    /* code modified by LLM (iteration 4): Use usize for executable loop and byte array access */
    while i < len / 2
        invariant
            0 <= i <= len / 2,
            len == text@.len(),
            forall|j: int| 0 <= j < i ==> text@[j] == text@[text@.len() - 1 - j],
            text_bytes@.len() == text@.len(),
            forall|k: int| 0 <= k < text@.len() ==> text_bytes@[k] == text@[k],
    {
        /* code modified by LLM (iteration 4): Use executable byte array indexing */
        let char1 = text_bytes[i];
        let char2 = text_bytes[len - 1 - i];
        
        if char1 != char2 {
            /* code modified by LLM (iteration 4): Add proof block to establish postcondition when returning false */
            proof {
                assert(text@[i as int] != text@[text@.len() - 1 - (i as int)]);
                assert(!(forall|j: int| 0 <= j < text@.len() ==> text@[j] == text@[text@.len() - 1 - j]));
            }
            return false;
        }
        i = i + 1;
    }
    
    /* code modified by LLM (iteration 4): Add proof block to establish postcondition when returning true */
    proof {
        assert(forall|j: int| 0 <= j < len / 2 ==> text@[j] == text@[text@.len() - 1 - j]);
        assert(forall|j: int| 0 <= j < text@.len() ==> text@[j] == text@[text@.len() - 1 - j]);
    }
    
    true
}

}
fn main() {}