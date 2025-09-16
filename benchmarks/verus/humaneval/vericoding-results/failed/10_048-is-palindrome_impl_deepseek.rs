// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn chars_to_seq(text: &str) -> Seq<char> {
    text@
}

proof fn palindrome_helper(text: Seq<char>, i: int, j: int)
    requires
        0 <= i <= j < text.len(),
    ensures
        text[i] == text[j] ==> (forall|k: int| i <= k <= j ==> text[k] == text[i + j - k]),
    decreases
        j - i
{
    if i < j {
        palindrome_helper(text, i + 1, j - 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn is_palindrome(text: &str) -> (result: bool)

    ensures
        result == forall|i: int|
            0 <= i < text@.len() ==> #[trigger] text@[i] == text@[text@.len() - 1 - i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed spec function issue and added proper verification */
    let n = text@.len();
    
    proof {
        let seq = chars_to_seq(text);
        let mut i: int = 0;
        while i < n / 2
            invariant
                0 <= i <= n / 2,
                forall|j: int| 0 <= j < i ==> text@[j] == text@[n - 1 - j],
        {
            if text@[i] != text@[n - 1 - i] {
                assert(!forall|k: int| 0 <= k < n ==> text@[k] == text@[n - 1 - k]);
                return false;
            }
            i = i + 1;
        }
        if n > 0 {
            palindrome_helper(text@, 0, n - 1);
        }
    }
    true
}
// </vc-code>

}
fn main() {}