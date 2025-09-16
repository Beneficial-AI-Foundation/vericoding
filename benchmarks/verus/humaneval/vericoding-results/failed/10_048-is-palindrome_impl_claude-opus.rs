// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_palindrome(text: &str) -> (result: bool)

    ensures
        result == forall|i: int|
            0 <= i < text@.len() ==> #[trigger] text@[i] == text@[text@.len() - 1 - i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Removed unnecessary cast from nat to usize */
    let text_seq = text@;
    let len = text_seq.len();
    
    if len == 0 {
        return true;
    }
    
    let mut i: nat = 0;
    let mut is_palindrome = true;
    
    while i < len / 2
        invariant
            0 <= i <= len / 2,
            is_palindrome == forall|j: int| 0 <= j < i ==> text_seq[j] == text_seq[text_seq.len() - 1 - j],
    {
        if text_seq[i as int] != text_seq[(len - 1 - i) as int] {
            is_palindrome = false;
            proof {
                assert(!forall|j: int| 0 <= j < text_seq.len() ==> text_seq[j] == text_seq[text_seq.len() - 1 - j]) by {
                    assert(!(text_seq[i as int] == text_seq[(text_seq.len() - 1 - i) as int]));
                }
            }
            return is_palindrome;
        }
        i = i + 1;
    }
    
    proof {
        assert(is_palindrome == forall|j: int| 0 <= j < text_seq.len() ==> text_seq[j] == text_seq[text_seq.len() - 1 - j]) by {
            assert forall|k: int| 0 <= k < text_seq.len() implies text_seq[k] == text_seq[text_seq.len() - 1 - k] by {
                if k < text_seq.len() / 2 {
                    assert(text_seq[k] == text_seq[text_seq.len() - 1 - k]);
                } else {
                    let k_mirror = text_seq.len() - 1 - k;
                    assert(0 <= k_mirror < text_seq.len() / 2);
                    assert(text_seq[k_mirror] == text_seq[text_seq.len() - 1 - k_mirror]);
                    assert(text_seq.len() - 1 - k_mirror == k);
                }
            }
        }
    }
    
    is_palindrome
}
// </vc-code>

}
fn main() {}