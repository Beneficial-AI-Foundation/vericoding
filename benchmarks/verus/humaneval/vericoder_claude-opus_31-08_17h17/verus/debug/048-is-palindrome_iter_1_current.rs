use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
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
    let text_view = text@;
    let len = text_view.len();
    
    if len == 0 {
        return true;
    }
    
    let mut i: usize = 0;
    while i < len / 2
        invariant
            0 <= i <= len / 2,
            len == text_view.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] text_view[j] == text_view[len - 1 - j],
    {
        if text_view[i as int] != text_view[len - 1 - i as int] {
            assert(!(text_view[i as int] == text_view[len - 1 - i as int]));
            return false;
        }
        i = i + 1;
    }
    
    // At this point, we've verified the first half matches the second half
    // Now we need to prove that ALL indices satisfy the palindrome property
    assert(i == len / 2);
    assert(forall|j: int| 0 <= j < len / 2 ==> #[trigger] text_view[j] == text_view[len - 1 - j]);
    
    // Prove the second half also satisfies the property by symmetry
    assert forall|k: int| len / 2 <= k < len implies #[trigger] text_view[k] == text_view[len - 1 - k] by {
        let mirror_k = len - 1 - k;
        assert(0 <= mirror_k < len / 2);
        assert(text_view[mirror_k] == text_view[len - 1 - mirror_k]);
        assert(len - 1 - mirror_k == k);
    }
    
    true
}
// </vc-code>

fn main() {}
}