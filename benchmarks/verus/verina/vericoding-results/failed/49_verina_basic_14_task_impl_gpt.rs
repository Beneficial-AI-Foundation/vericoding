// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate for checking if a character is 'z' or 'Z' */
spec fn is_z(c: char) -> bool { c == 'z' || c == 'Z' }
/* helper modified by LLM (iteration 5): spec predicate that states whether a Seq<char> contains a 'z' or 'Z' */
spec fn contains_z_seq(s: Seq<char>) -> bool { exists|i: int| 0 <= i < s.len() && is_z(s[i]) }
// </vc-helpers>

// <vc-spec>
fn contains_z(s: &str) -> (result: bool)
    ensures
        result <==> exists|i: int| 0 <= i < s@.len() && (s@[i] == 'z' || s@[i] == 'Z'),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute using str::contains for 'z' or 'Z' */
    s.contains('z') || s.contains('Z')
}
// </vc-code>

}
fn main() {}