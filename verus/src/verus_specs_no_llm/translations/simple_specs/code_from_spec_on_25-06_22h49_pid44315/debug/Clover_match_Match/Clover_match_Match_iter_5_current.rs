use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Match(s: String, p: String) -> (b: bool)
    requires
        s.len() == p.len()
    ensures
        b <==> forall |n: int| 0 <= n < s.len() ==> s.spec_index(n) == p.spec_index(n) || p.spec_index(n) == '?' as char
{
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall |n: int| 0 <= n < i ==> s.spec_index(n) == p.spec_index(n) || p.spec_index(n) == '?' as char
    {
        // Use the strings directly with indexing
        let s_bytes = s.as_bytes();
        let p_bytes = p.as_bytes();
        
        // Get bytes at position i
        let s_byte = s_bytes[i];
        let p_byte = p_bytes[i];
        
        // For the matching condition, we need to check if the pattern byte is '?' or matches
        if s_byte != p_byte && p_byte != ('?' as char) as u8 {
            // Use a proof block to establish the contradiction
            proof {
                // At position i, we have a mismatch and pattern is not '?'
                // This means the postcondition should be false
                let n = i as int;
                assert(0 <= n < s.len());
                
                // The key insight: we can reason about the relationship between
                // bytes and spec_index for valid UTF-8 characters
                assert(s.spec_index(n) != p.spec_index(n));
                assert(p.spec_index(n) != '?' as char);
                assert(!(s.spec_index(n) == p.spec_index(n) || p.spec_index(n) == '?' as char));
                
                // Therefore, the universal quantification is false
                assert(!forall |k: int| 0 <= k < s.len() ==> s.spec_index(k) == p.spec_index(k) || p.spec_index(k) == '?' as char);
            }
            return false;
        }
        
        // If we reach here, either s_byte == p_byte or p_byte == '?' as u8
        proof {
            let n = i as int;
            assert(0 <= n < s.len());
            // This position satisfies the matching condition
            assert(s.spec_index(n) == p.spec_index(n) || p.spec_index(n) == '?' as char);
        }
        
        i += 1;
    }
    
    // When we exit the loop, we've verified all positions match
    proof {
        assert(i == s.len());
        // The loop invariant gives us the postcondition
        assert(forall |n: int| 0 <= n < s.len() ==> s.spec_index(n) == p.spec_index(n) || p.spec_index(n) == '?' as char);
    }
    
    return true;
}

}