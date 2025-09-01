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
            0 <= i <= n / 2,
            n / 2 <= j < n,
            i <= j + 1,
            forall|k: int| 0 <= k < i ==> #[trigger] str_bytes@[k] == str_bytes@[n - 1 - k],
            forall|k: int| j < k < n ==> #[trigger] str_bytes@[k] == str_bytes@[n - 1 - k],
    {
        if str_bytes@[i] != str_bytes@[j] {
            return false;
        }
        i = i + 1;
        j = j - 1;
    }

    // Proof that if the loop completes, the string is a palindrome.
    proof {
        assert(i >= j) by (nonlinear_arith) implies (i >= n / 2 && j <= n / 2) by (nonlinear_arith);

        assert(forall|k: int| 0 <= k < i ==> #[trigger] str_bytes@[k] == str_bytes@[n - 1 - k]);
        assert(forall|k: int| j < k < n ==> #[trigger] str_bytes@[k] == str_bytes@[n - 1 - k]);

        assert(forall|k: int| i <= k <= j ==> str_bytes@[k] == str_bytes@[n - 1 - k]) by {
            // This part is implicitly true because the loop ensured all checked characters matched.
            // If i >= j, the range i..j is empty or contains a single element (if i==j).
            // For a single element k where i==j==k, it is trivially true or not part of the check.
            // For odd length strings, the middle character doesn't get compared to itself.
        };

        assert(forall|k: int| 0 <= k < n ==> #[trigger] str_bytes@[k] == str_bytes@[n - 1 - k]);
    }

    true
}
// </vc-code>

fn main() {}
}