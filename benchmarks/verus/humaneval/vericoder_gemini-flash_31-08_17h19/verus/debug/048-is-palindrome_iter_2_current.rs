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
        assert(i >= j) implies (i >= n / 2 && j <= n / 2); // Removed `by (nonlinear_arith)` as it was causing a syntax error.

        assert(forall|k: int| 0 <= k < i ==> #[trigger] str_bytes@[k] == str_bytes@[n - 1 - k]);
        assert(forall|k: int| j < k < n ==> #[trigger] str_bytes@[k] == str_bytes@[n - 1 - k]);

        // The assertion about the middle part (i <= k <= j) being true is implicitly handled
        // because upon loop termination, `i >= j`. This means the range `i..j` is either empty
        // or contains a single character if `n` is odd and `i == j`. In either case, all
        // characters up to `i` and from `j+1` have been verified.
        // If `n` is even, `i` effectively becomes `n/2` and `j` becomes `n/2 - 1`, making `i > j`.
        // If `n` is odd, `i` and `j` will both eventually point to the middle character at `n/2`,
        // and the loop will terminate because `i` is no longer less than `j`.
        // The characters handled by `0 <= k < i` and `j < k < n` cover the entire string when `i >= j`.

        assert(forall|k: int| 0 <= k < n ==> #[trigger] str_bytes@[k] == str_bytes@[n - 1 - k]);
    }

    true
}
// </vc-code>

fn main() {}
}