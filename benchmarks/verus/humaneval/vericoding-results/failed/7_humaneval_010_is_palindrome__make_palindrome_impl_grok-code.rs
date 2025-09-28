// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_palindrome(s: Seq<char>) -> bool {
    forall|k: int| #![trigger s.index(k)] 0 <= k < s.len() ==> s.index(k) == s.index(s.len() - 1 - k)
}

spec fn starts_with(result: Seq<char>, s: Seq<char>) -> bool {
    result.len() >= s.len() && forall|k: int| #![trigger result.index(k)] 0 <= k < s.len() ==> result.index(k) == s.index(k)
}
// </vc-preamble>

// <vc-helpers>
spec fn reverse_seq(s: Seq<char>) -> Seq<char> {
    Seq::new(s.len(), |i| s[s.len() - 1 - i])
}

/* helper modified by LLM (iteration 5): fixed compilation error by declaring result variable */
fn reverse_str(s: &str) -> (result: String)
    ensures
        result@.len() == s@.len(),
        forall|i: int| 0 <= i < s@.len() ==> result@[i] == s@[s@.len() - 1 - i]
{
    let rev_chars: Vec<char> = s.chars().rev().collect();
    let result = rev_chars.into_iter().collect::<String>();
    proof {
        assert(result@ == reverse_seq(s@));
        assert(forall|i: int| 0 <= i < s@.len() ==> result@[i] == s@[s@.len() - 1 - i]);
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn make_palindrome(s: &str) -> (result: String)
    ensures 
        result@.len() <= 2 * s@.len(),
        is_palindrome(result@),
        starts_with(result@, s@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implemented make_palindrome by concatenating string with its reverse */
    let mut result = s.to_string();
    let rev = reverse_str(s);
    result.push_str(&rev);
    proof {
        assert(reverse_seq(s@) == rev@);
        assert(is_palindrome(s@ + reverse_seq(s@)));
        // Length condition: result@@.len() == 2 * s@@.len() <= 2 * s@@.len()
        // Starts_with: by construction, first s@.len() are s@
    }
    result
}
// </vc-code>


}

fn main() {}