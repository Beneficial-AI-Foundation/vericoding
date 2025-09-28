// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn isPalindrome(s: &Vec<char>) -> (result: bool)
    requires 1 <= s.len() <= 200000,
    ensures result <==> (forall|i: int| 0 <= i < (s.len() as int) / 2 ==> s[i] == s[(s.len() as int) - 1 - i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added trigger to invariant and specific assertion for false path */
    let mut i: usize = 0;
    let n = s.len();
    while i < n / 2
        invariant
            0 <= i <= n / 2,
            forall|j: int| 0 <= j < (i as int) ==> #[trigger] s@[j] == s@[(n as int) - 1 - j],
        decreases n / 2 - i
    {
        if s[i] != s[n - 1 - i] {
            // To prove the postcondition when returning `false`, we need to show
            // that the palindrome property `forall ...` is false.
            // This is equivalent to showing `exists k :: ...` where the property fails.
            // The current loop index `i` is the witness for this existence.
            assert(exists|k: int| 0 <= k < (n as int) / 2 && s@[k] != s@[(n as int) - 1 - k]);
            return false;
        }
        i = i + 1;
    }

    true
}
// </vc-code>

}
fn main() {}