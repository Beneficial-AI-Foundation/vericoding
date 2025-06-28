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
        // Get characters at position i using actual indexing for executable code
        let s_bytes = s.as_bytes();
        let p_bytes = p.as_bytes();
        let s_char = s_bytes[i] as char;
        let p_char = p_bytes[i] as char;
        
        // Check if characters match or pattern has wildcard
        if s_char != p_char && p_char != '?' {
            proof {
                // Connect the executable values to the spec values
                assert(s.spec_index(i as int) == s_char);
                assert(p.spec_index(i as int) == p_char);
                
                // At position i, we have a mismatch and pattern is not '?'
                let n = i as int;
                assert(0 <= n < s.len());
                assert(s.spec_index(n) != p.spec_index(n));
                assert(p.spec_index(n) != '?' as char);
                assert(!(s.spec_index(n) == p.spec_index(n) || p.spec_index(n) == '?' as char));
                
                // Therefore, the postcondition should be false
                assert(!forall |k: int| 0 <= k < s.len() ==> s.spec_index(k) == p.spec_index(k) || p.spec_index(k) == '?' as char);
            }
            return false;
        }
        
        proof {
            // Connect the executable values to the spec values
            assert(s.spec_index(i as int) == s_char);
            assert(p.spec_index(i as int) == p_char);
            
            // If we reach here, either s_char == p_char or p_char == '?'
            let n = i as int;
            assert(0 <= n < s.len());
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