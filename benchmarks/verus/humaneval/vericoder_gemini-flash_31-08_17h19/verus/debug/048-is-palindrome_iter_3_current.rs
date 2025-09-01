use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier(external_body)]
#[cfg(feature = "is_palindrome")]
pub exec fn get_string_length(s: &str) -> usize {
    s.len()
}

#[verifier(external_body)]
#[cfg(feature = "is_palindrome")]
pub exec fn get_char_at_string(s: &str, i: usize) -> char {
    s.as_bytes()[i] as char
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
    let str_bytes = text.as_bytes();
    let n = str_bytes.len();

    let mut i: int = 0;
    let mut j: int = (n - 1) as int;

    while i < j
        invariant
            0 <= i <= (n as int + 1) / 2, // i must not exceed the middle index
            (n as int - 1) / 2 <= j < n as int, // j must not be less than the middle index
            i <= j + 1,
            forall|k: int| 0 <= k < i ==> #[trigger] str_bytes@[k] == str_bytes@[(n as int) - 1 - k],
            forall|k: int| j < k < n as int ==> #[trigger] str_bytes@[k] == str_bytes@[(n as int) - 1 - k],
    {
        if str_bytes@[i] != str_bytes@[j] {
            return false;
        }
        i = i + 1;
        j = j - 1;
    }

    // Proof that if the loop completes, the string is a palindrome.
    proof {
        // Assert invariants hold at loop termination
        assert(i >= j);
        assert(0 <= i <= (n as int + 1) / 2);
        assert((n as int - 1) / 2 <= j < n as int);

        // The core proof that the string is a palindrome.
        // We need to show that for any k from 0 to n-1, str_bytes[k] == str_bytes[n-1-k].
        assert forall|k: int| 0 <= k < n as int implies #[trigger] str_bytes@[k] == str_bytes@[(n as int) - 1 - k] by {
            if 0 <= k < i {
                // This case is covered by the loop invariant.
                assert(str_bytes@[k] == str_bytes@[(n as int) - 1 - k]);
            } else if j < k < n as int {
                // This case is also covered by the loop invariant.
                assert(str_bytes@[k] == str_bytes@[(n as int) - 1 - k]);
            } else { // i <= k <= j
                // If i <= k <= j holds at termination, it implies n is odd and k is the middle element.
                // In this scenario, i == j == k == (n-1)/2. For such a k, n-1-k = n-1-(n-1)/2 = (n-1)/2 = k.
                // So str_bytes[k] == str_bytes[n-1-k] is trivially true.
                // This path is only taken if n is odd and i == j at termination.
                // Otherwise (n is even), i = n/2 and j = n/2 - 1, meaning i > j. So k in [i, j] is an empty range.
                if n % 2 == 1 {
                    assert (i == j);
                    assert (k == i);
                    assert (str_bytes@[k] == str_bytes@[(n as int) - 1 - k]);
                } else {
                    // If n is even, i = n / 2 and j = n / 2 - 1. So i > j and the range [i, j] is empty.
                    // This 'else' branch is unreachable if all elements are covered.
                    // Verus will infer this if the previous two cases cover all possible 'k'.
                }
            }
        };
    }

    true
}
// </vc-code>

fn main() {}
}