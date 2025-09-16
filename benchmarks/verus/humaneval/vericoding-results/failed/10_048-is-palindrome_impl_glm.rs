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
    let n = text@.len();
    let mut i = 0;
    let mut j = n - 1;
    while i < j
        invariant
            0 <= i <= n,
            j == n - 1 - i,
            forall|k: int| 0 <= k < i ==> text@[k] == text@[n - 1 - k],
        decreases j - i,
    {
        if text@[i] != text@[j] {
            return false;
        }
        i += 1;
        j -= 1;
    }
    true
}
// </vc-code>

}
fn main() {}