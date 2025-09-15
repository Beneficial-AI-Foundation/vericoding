// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_char_at_matches(s_seq: Seq<char>, p_seq: Seq<char>, idx: int) 
    requires 
        0 <= idx < s_seq.len(), 
        s_seq.len() == p_seq.len(), 
        s_seq.index(idx) == p_seq.index(idx) || p_seq.index(idx) == '?' as char 
    ensures 
        s_seq.index(idx) == p_seq.index(idx) || p_seq.index(idx) == '?' as char 
{ 
    // This lemma trivially holds by its requires clause. 
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
    let s_seq = s@;
    let p_seq = p@;
    let mut i = 0;
    let mut all_match = true;

    while i < s_seq.len() 
        invariant 
            0 <= i <= s_seq.len(), 
            s_seq.len() == p_seq.len(), 
            all_match == (forall|n: int| 0 <= n < i ==> 
                (s_seq.index(n) == p_seq.index(n) || p_seq.index(n) == '?' as char))
    {
        let s_char = s_seq.index(i);
        let p_char = p_seq.index(i);
        
        if s_char == p_char || p_char == '?' as char {
            // Characters match or pattern has '?'
        } else {
            all_match = false;
            break;
        }
        i = i + 1;
    }
    
    all_match
}
// </vc-code>

}
fn main() {}