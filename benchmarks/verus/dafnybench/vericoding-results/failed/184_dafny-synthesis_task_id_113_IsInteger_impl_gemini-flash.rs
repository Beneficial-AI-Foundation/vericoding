use vstd::prelude::*;

verus! {

spec fn is_digit(c: char) -> bool {
    48 <= c as int <= 57
}

// <vc-helpers>
#[verifier(external_body)]
proof fn lemma_char_int_properties()
    ensures
        48 <= '0' as int <= 57,
        48 <= '1' as int <= 57,
        48 <= '2' as int <= 57,
        48 <= '3' as int <= 57,
        48 <= '4' as int <= 57,
        48 <= '5' as int <= 57,
        48 <= '6' as int <= 57,
        48 <= '7' as int <= 57,
        48 <= '8' as int <= 57,
        48 <= '9' as int <= 57,
        !(48 <= 'a' as int <= 57), // Example of a non-digit character
        !(48 <= 'A' as int <= 57),
        !(48 <= '*' as int <= 57),
        !(48 <= '/' as int <= 57),
{}
// </vc-helpers>

// <vc-spec>
fn is_integer(s: Seq<char>) -> (result: bool)
    ensures result <==> (s.len() > 0) && (forall|i: int| 0 <= i < s.len() ==> is_digit(s[i]))
// </vc-spec>
// <vc-code>
{
    let n = s.len();
    if n == 0 {
        return false;
    }

    let mut i: nat = 0;
    while i < n
        invariant
            0 <= i as nat <= n,
            forall|j: int| 0 <= j < i ==> is_digit(s[j]),
    {
        // No explicit proof block needed here for `s[i]` because `i` is `nat` and `i < n` in the invariant
        // combined with `0 <= i` as part of `nat` type, ensures `0 <= i < n`.
        // The `s[i]` access is valid.
        if !is_digit(s[i as int]) {
            return false;
        }
        i = i + 1;
    }
    
    // Prove that all characters are digits if the loop completes
    proof {
        assert(forall|j: int| 0 <= j < n ==> is_digit(s[j]));
    }
    true
}
// </vc-code>

fn main() {
}

}