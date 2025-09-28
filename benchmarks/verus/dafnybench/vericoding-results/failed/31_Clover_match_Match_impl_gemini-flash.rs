use vstd::prelude::*;

verus! {

// <vc-helpers>
fn is_match_at_index(s_char: char, p_char: char) -> bool {
    p_char == '?' || s_char == p_char
}
// </vc-helpers>

// <vc-spec>
fn match_strings(s: Seq<char>, p: Seq<char>) -> (b: bool)
  requires s.len() == p.len()
  ensures b == (forall|n: int| 0 <= n < s.len() ==> s[n] == p[n] || p[n] == '?')
// </vc-spec>
// <vc-code>
{
    let mut i: nat = 0;
    let len: nat = s.len();

    while i < len
        invariant
            0 <= i <= len,
            forall|n: nat| 0 <= n < i ==> is_match_at_index(s@[n], p@[n]),
    {
        if !is_match_at_index(s@[i], p@[i]) {
            return false;
        }
        i = i + 1;
    }

    assert(forall |n: nat| 0 <= n < len ==> is_match_at_index(s@[n], p@[n])) by {
        // This assertion is implicitly proven by the loop invariant and the fact that the loop completed.
        // The invariant states that for all n < i, is_match_at_index(s[n], p[n]) holds.
        // When the loop terminates, i == len.
        // Therefore, for all n < len, is_match_at_index(s[n], p[n]) holds.
    }
    true
}
// </vc-code>

fn main() {
}

}