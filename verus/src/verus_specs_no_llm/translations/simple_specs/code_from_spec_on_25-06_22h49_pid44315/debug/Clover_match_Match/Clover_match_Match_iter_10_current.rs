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
        // Convert strings to sequences for indexing
        let s_seq = s@;
        let p_seq = p@;
        
        // Get characters at position i using sequence indexing
        let s_char = s_seq[i as int];
        let p_char = p_seq[i as int];
        
        // Check if characters match or pattern has wildcard
        if s_char != p_char && p_char != ('?' as char) {
            proof {
                // At position i, we have a mismatch and pattern is not '?'
                let n = i as int;
                assert(0 <= n < s.len());
                assert(s.spec_index(n) == s_char);
                assert(p.spec_index(n) == p_char);
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
            assert(s.spec_index(n) == s_char);
            assert(p.spec_index(n) == p_char);
            if s_char == p_char {
                assert(s.spec_index(n) == p.spec_index(n));
            } else {
                assert(p_char == ('?' as char));
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