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
        // Get characters at position i using spec_index in the specification
        // We need to use a ghost block to reason about the characters
        proof {
            assert(0 <= i < s.len());
        }
        
        let s_bytes = s.as_bytes();
        let p_bytes = p.as_bytes();
        
        // Get bytes at position i
        let s_byte = s_bytes[i];
        let p_byte = p_bytes[i];
        
        // Convert bytes to chars for comparison
        let s_char = s_byte as char;
        let p_char = p_byte as char;
        
        if s_char != p_char && p_char != ('?' as char) {
            // For the proof, we need to establish that the spec_index characters
            // correspond to our runtime characters
            proof {
                // The key insight: for ASCII strings, byte-to-char conversion
                // should match spec_index behavior
                assert(s.spec_index(i as int) == s_char);
                assert(p.spec_index(i as int) == p_char);
                assert(!(s.spec_index(i as int) == p.spec_index(i as int) || p.spec_index(i as int) == '?' as char));
            }
            return false;
        }
        
        // Maintain the loop invariant
        proof {
            assert(s.spec_index(i as int) == s_char);
            assert(p.spec_index(i as int) == p_char);
            assert(s.spec_index(i as int) == p.spec_index(i as int) || p.spec_index(i as int) == '?' as char);
        }
        
        i += 1;
    }
    
    // When we exit the loop, we've checked all positions
    proof {
        assert(i == s.len());
        assert(forall |n: int| 0 <= n < s.len() ==> s.spec_index(n) == p.spec_index(n) || p.spec_index(n) == '?' as char);
    }
    
    return true;
}

}