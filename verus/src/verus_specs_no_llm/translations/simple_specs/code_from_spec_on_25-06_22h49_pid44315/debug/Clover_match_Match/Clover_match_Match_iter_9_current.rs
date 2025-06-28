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
        // Get characters at position i using regular indexing for executable code
        let s_char = s.as_bytes()[i];
        let p_char = p.as_bytes()[i];
        
        // Check if characters match or pattern has wildcard
        if s_char != p_char && p_char != ('?' as u8) {
            proof {
                // At position i, we have a mismatch and pattern is not '?'
                let n = i as int;
                assert(0 <= n < s.len());
                // Connect executable indexing to spec indexing
                assert(s.as_bytes()[i] == s.spec_index(n) as u8);
                assert(p.as_bytes()[i] == p.spec_index(n) as u8);
                assert(s.spec_index(n) != p.spec_index(n));
                assert(p.spec_index(n) != '?' as char);
                assert(!(s.spec_index(n) == p.spec_index(n) || p.spec_index(n) == '?' as char));
                
                // Therefore, the postcondition should be false
                assert(!forall |k: int| 0 <= k < s.len() ==> s.spec_index(k) == p.spec_index(k) || p.spec_index(k) == '?' as char);
            }
            return false;
        }
        
        proof {
            // If we reach here, either s_char == p_char or p_char == '?'
            let n = i as int;
            assert(0 <= n < s.len());
            // Connect executable indexing to spec indexing
            assert(s.as_bytes()[i] == s.spec_index(n) as u8);
            assert(p.as_bytes()[i] == p.spec_index(n) as u8);
            if s_char == p_char {
                assert(s.spec_index(n) == p.spec_index(n));
            } else {
                assert(p_char == ('?' as u8));
                assert(p.spec_index(n) == '?' as char);
            }
            assert(s.spec_index(n) == p.spec_index(n) || p.spec_index(n) == '?' as char);
        }
        
        i += 1;
    }
    
    // When we exit the loop, we've verified all positions match
    proof {
        assert(i == s.len());
        assert(forall |n: int| 0 <= n < s.len() ==> s.spec_index(n) == p.spec_index(n) || p.spec_index(n) == '?' as char);
    }
    
    return true;
}

}