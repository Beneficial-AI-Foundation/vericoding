// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_space_comma_dot(c: char) -> bool
{
    c == ' ' || c == ',' || c == '.'
}
// </vc-preamble>

// <vc-helpers>
spec fn map_char(c: char) -> char
{
    if is_space_comma_dot(c) { ':' } else { c }
}

spec fn mapped_seq(s: Seq<char>) -> Seq<char>
{
    Seq::new(s.len(), |i: int| map_char(s.index(i)))
}
// </vc-helpers>

// <vc-spec>
fn replace_with_colon(s: &str) -> (result: String)
    ensures
        result@.len() == s@.len(),
        forall|i: int| 0 <= i < s@.len() ==> 
            #[trigger] result@.index(i) == 
            if is_space_comma_dot(#[trigger] s@.index(i)) { ':' } else { s@.index(i) },
// </vc-spec>
// <vc-code>
{
    let result = String::from_chars(mapped_seq(s@));
    result
}
// </vc-code>

}
fn main() {}