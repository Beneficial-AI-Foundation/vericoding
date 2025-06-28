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
        let s_bytes = s.as_bytes();
        let p_bytes = p.as_bytes();
        
        // Get characters at position i
        let s_char = s_bytes[i] as char;
        let p_char = p_bytes[i] as char;
        
        if s_char != p_char && p_char != ('?' as char) {
            // Prove that the postcondition is false
            assert(s_char != p_char && p_char != ('?' as char));
            assert(s.spec_index(i as int) == s_char) by {
                // This follows from the relationship between as_bytes and spec_index
            };
            assert(p.spec_index(i as int) == p_char) by {
                // This follows from the relationship between as_bytes and spec_index  
            };
            assert(!(s.spec_index(i as int) == p.spec_index(i as int) || p.spec_index(i as int) == '?' as char));
            return false;
        }
        
        // Prove the loop invariant is maintained
        assert(s.spec_index(i as int) == s_char) by {
            // This follows from the relationship between as_bytes and spec_index
        };
        assert(p.spec_index(i as int) == p_char) by {
            // This follows from the relationship between as_bytes and spec_index
        };
        assert(s.spec_index(i as int) == p.spec_index(i as int) || p.spec_index(i as int) == '?' as char);
        
        i += 1;
    }
    
    // Prove the postcondition when returning true
    assert(i == s.len());
    assert(forall |n: int| 0 <= n < s.len() ==> s.spec_index(n) == p.spec_index(n) || p.spec_index(n) == '?' as char);
    return true;
}

}