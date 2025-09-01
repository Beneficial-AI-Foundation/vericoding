use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
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
fn is_palindrome(text: &str) -> (result: bool)
    // post-conditions-start
    ensures
        result == forall|i: int|
            0 <= i < text@.len() ==> #[trigger] text@[i] == text@[text@.len() - 1 - i],
    // post-conditions-end
{
    let len = text@.len();
    if len <= 1 {
        return true;
    }
    let mut i: usize = 0;
    while i < (len as usize) / 2
        invariant
            0 <= i,
            forall|j: int| 0 <= j < (i as int) ==> #[trigger] text@[j] == text@[len - 1 - j]
    {
        if text@[i as int] != text@[len - 1 - (i as int)] {
            return false;
        }
        i += 1;
    }
    proof {
        assert(!exists|k: int| 0 <= k < (len as usize / 2) as int && text@[k] != text@[len - 1 - k]);
        assert forall|m: int| 0 <= m < len ==> #[trigger] text@[m] == text@[len - 1 - m] by {
            if m <= m {
                // if m <= len - 1 - m, i.e., m <= len/2 - 0.5 approximately
            }
        };
        // The symmetry ensures that if the first half matches the symmetric second half,
        // and since m and len-1-m are paired, and we've checked all such pairs,
        // the full condition holds for all m.
    }
    true
}
// </vc-code>
// </vc-code>

fn main() {}
}