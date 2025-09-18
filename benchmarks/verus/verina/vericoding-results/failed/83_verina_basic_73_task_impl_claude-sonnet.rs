// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added helper function to get string length */
fn str_len(s: &str) -> (len: usize)
    ensures len == s@.len()
{
    s.unicode_len()
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
{
    /* code modified by LLM (iteration 5): use ghost variables for character indexing */
    let mut i = 0;
    let s_len = str_len(s);
    let p_len = str_len(p);
    
    while i < s_len
        invariant
            0 <= i <= s@.len(),
            s@.len() == p@.len(),
            s_len == s@.len(),
            p_len == p@.len(),
            forall|n: int| 0 <= n < i ==> (s@.index(n) == p@.index(n) || p@.index(n) == '?' as u8),
    {
        proof {
            let ghost s_char = s@.index(i as int);
            let ghost p_char = p@.index(i as int);
            
            if s_char != p_char && p_char != '?' as u8 {
                return false;
            }
        }
        i += 1;
    }
    true
}
// </vc-code>

}
fn main() {}