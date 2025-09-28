// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Use byte-based iteration to match postcondition */
    let mut i: usize = 0;
    let s_bytes = s@;
    let p_bytes = p@;
    let len = s_bytes.len();
    
    while i < len
        invariant
            i <= len,
            len == s_bytes.len(),
            len == p_bytes.len(),
            s_bytes == s@,
            p_bytes == p@,
            forall|n: int| 0 <= n < i as int ==> (s_bytes.index(n) == p_bytes.index(n) || p_bytes.index(n) == '?' as u8),
        decreases len - i,
    {
        let s_byte = s.get_byte(i);
        let p_byte = p.get_byte(i);
        
        if s_byte != p_byte && p_byte != ('?' as u8) {
            // Assert that we found a mismatch
            assert(!(s@.index(i as int) == p@.index(i as int) || p@.index(i as int) == '?' as u8));
            assert(exists|n: int| 0 <= n < s@.len() && !(s@.index(n) == p@.index(n) || p@.index(n) == '?' as u8));
            return false;
        }
        i = i + 1;
    }
    
    // Assert that all positions match
    assert(forall|n: int| 0 <= n < s@.len() ==> (s@.index(n) == p@.index(n) || p@.index(n) == '?' as u8));
    true
}
// </vc-code>

}
fn main() {}