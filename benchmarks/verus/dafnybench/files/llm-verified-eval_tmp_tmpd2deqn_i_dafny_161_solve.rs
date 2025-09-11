// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_letter(c: char) -> bool {
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
}

spec fn no_letters(s: Seq<char>, n: nat) -> bool
    recommends n <= s.len()
{
    forall|i: int| 0 <= i < n ==> !is_letter(s[i])
}

spec fn toggle_case(c: char) -> char {
    if c >= 'a' && c <= 'z' {
        ((c as u8 - 'a' as u8 + 'A' as u8) as char)
    } else if c >= 'A' && c <= 'Z' {
        ((c as u8 - 'A' as u8 + 'a' as u8) as char)
    } else {
        c
    }
}

spec fn is_reverse(s: Seq<char>, s_prime: Seq<char>) -> bool {
    (s.len() == s_prime.len()) &&
    (forall|si: int| 0 <= si < s.len()/2 ==> s_prime[s.len() - si - 1] == s[si])
}

fn reverse(original: Vec<char>) -> (reversed: Vec<char>)
    ensures 
        reversed@.len() == original@.len(),
        forall|i: int| 0 <= i < original@.len() ==> reversed@[i] == original@[original@.len() - 1 - i]
{
    assume(false);
    vec![]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    ensures 
        result@.len() == s@.len(),
        !no_letters(s@, s@.len() as nat) ==> 
            forall|i: int| 0 <= i < s@.len() && is_letter(s@[i]) ==> 
                result@[i] == toggle_case(s@[i]),
        !no_letters(s@, s@.len() as nat) ==> 
            forall|i: int| 0 <= i < s@.len() && !is_letter(s@[i]) ==> 
                result@[i] == s@[i],
        no_letters(s@, s@.len() as nat) ==> is_reverse(result@, s@)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}