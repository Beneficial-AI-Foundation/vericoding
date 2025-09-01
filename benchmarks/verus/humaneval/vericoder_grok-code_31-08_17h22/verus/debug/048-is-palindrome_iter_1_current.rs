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
    let chars = text.as_bytes();
    let len_usize: usize = chars.len();
    let len_int: int = chars@.len();
    if len_int <= 1 {
        true
    } else {
        let mut i: usize = 0;
        while i < len_usize / 2
            invariant
                0 <= i <= len_usize / 2,
                forall|j: int| 0 <= j < i as int ==> #[trigger] chars@[j] == chars@[len_int - 1 - j]
        {
            if chars[i] != chars[len_usize - 1 - i] {
                return false;
            }
            i = i + 1;
        }
        // Now prove the full forall using symmetry
        proof {
            assert(!exists|k: int| 0 <= k < len_int / 2 && chars@[k] != chars@[len_int - 1 - k]);
            assert forall|m: int| 0 <= m < len_int ==> #[trigger] chars@[m] == chars@[len_int - 1 - m] by {
                let n = len_int - 1 - m;
                if m == n {
                    // trivial
                } else if m < n {
                    if m < len_int / 2 {
                        // by the non-existence of mismatch up to len_int / 2
                    }
                } else {
                    // symmetry from the other side
                }
            };
        }
        true
    }
}
// </vc-code>
// </vc-code>

fn main() {}
}