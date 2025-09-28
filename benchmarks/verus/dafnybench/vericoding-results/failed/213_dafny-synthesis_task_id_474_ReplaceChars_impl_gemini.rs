// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn replace_chars(s: Seq<char>, old_char: char, new_char: char) -> (v: Seq<char>)
    ensures
        v.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> 
            (s[i] == old_char ==> v[i] == new_char) &&
            (s[i] != old_char ==> v[i] == s[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): The function signature uses ghost types (Seq), so it must be a 'spec' function. The body must be a ghost expression, not executable code with a 'while' loop. Re-implemented with 's.map'. */
    s.map(|_idx: int, c: char| if c == old_char { new_char } else { c })
}
// </vc-code>

}
fn main() {}