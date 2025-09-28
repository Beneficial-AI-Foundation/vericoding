// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added helper to avoid using as_bytes() in spec */
spec fn match_strings_spec(s: Seq<u8>, p: Seq<u8>) -> bool {
    forall|n: int| 0 <= n < s.len() ==> (s[n] == p[n] || p[n] == '?' as u8)
}
// </vc-helpers>

// <vc-spec>
fn match_strings(s: &str, p: &str) -> (result: bool)
    requires s@.len() == p@.len(),
    ensures
        result == (forall|n: int| 0 <= n < s@.len() ==> 
            (s@.index(n) == p@.index(n) || p@.index(n) == '?' as u8)),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Avoid as_bytes() by comparing character by character using chars() iterator */
{
    let mut s_chars = s.chars();
    let mut p_chars = p.chars();
    let len = s@.len();
    
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            forall|n: int| 0 <= n < i ==> (s@[n] == p@[n] || p@[n] == '?' as u8),
    {
        let s_char = s_chars.next().unwrap();
        let p_char = p_chars.next().unwrap();
        if p_char != '?' && s_char != p_char {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}