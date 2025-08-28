use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn is_palindrome_spec(text: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < text.len() ==> text[i] == text[text.len() - 1 - i]
}
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
    let len = text@.len();
    let mut i: usize = 0;
    
    while i < len / 2
        invariant
            0 <= i <= len / 2,
            forall|j: int| 0 <= j < i ==> text@[j] == text@[len - 1 - j],
    {
        if text@[i as int] != text@[(len - 1 - i) as int] {
            return false;
        }
        i += 1;
    }
    
    true
}
// </vc-code>

}
fn main() {}