// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes made */
proof fn palindrome_symmetry(s: Seq<char>)
    requires
        forall|i: int| 0 <= i < s.len() / 2 ==> #[trigger] s[i] == s[s.len() - 1 - i],
    ensures
        forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] == s[s.len() - 1 - i],
{
}
// </vc-helpers>

// <vc-spec>
fn is_palindrome(text: &str) -> (result: bool)

    ensures
        result == forall|i: int|
            0 <= i < text@.len() ==> #[trigger] text@[i] == text@[text@.len() - 1 - i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed compilation error by using the correct lemma name */
{
    let s_chars: Vec<char> = text.chars().collect();
    proof {
        vstd::string::lemma_string_chars_are_vector_chars(text, &s_chars);
        assert(text@ == s_chars@);
    }
    let len = s_chars.len();

    let mut i: usize = 0;
    while i < len / 2
        invariant
            i <= len / 2,
            text@ == s_chars@,
            forall|k: int| 0 <= k < i as int ==> text@[k] == text@[text@.len() - 1 - k],
        decreases (len / 2) - i
    {
        if s_chars[i] != s_chars[len - 1 - i] {
            proof {
                assert(text@[i as int] != text@[text@.len() - 1 - (i as int)]);
                assert(!(forall|j: int| 0 <= j < text@.len() ==> #[trigger] text@[j] == text@[text@.len() - 1 - j]));
            }
            return false;
        }
        i = i + 1;
    }

    proof {
        palindrome_symmetry(text@);
    }
    
    true
}
// </vc-code>

}
fn main() {}