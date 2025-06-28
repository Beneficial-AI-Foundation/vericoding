use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ContainsZ(s: &str) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < s.len() && (s.spec_index(i) == 'z' || s.spec_index(i) == 'Z'))
{
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < i ==> !(s.spec_index(j) == 'z' || s.spec_index(j) == 'Z'),
    {
        let bytes = s.as_bytes();
        let byte_val = bytes[i];
        
        // Check if the byte corresponds to 'z' or 'Z'
        if byte_val == 122u8 || byte_val == 90u8 {  // 122 = 'z', 90 = 'Z'
            assert(exists|k: int| 0 <= k < s.len() && (s.spec_index(k) == 'z' || s.spec_index(k) == 'Z')) by {
                assert(0 <= i < s.len());
                assert(byte_val == 122u8 || byte_val == 90u8);
                // The key insight: if the byte is 122 or 90, then spec_index gives us 'z' or 'Z'
                assert(s.spec_index(i as int) == 'z' || s.spec_index(i as int) == 'Z');
            };
            return true;
        }
        
        assert(!(s.spec_index(i as int) == 'z' || s.spec_index(i as int) == 'Z')) by {
            assert(byte_val != 122u8 && byte_val != 90u8);
            // If byte is not 122 or 90, then spec_index doesn't give us 'z' or 'Z'
        };
        i += 1;
    }
    
    assert(forall|j: int| 0 <= j < s.len() ==> !(s.spec_index(j) == 'z' || s.spec_index(j) == 'Z'));
    assert(!(exists|i: int| 0 <= i < s.len() && (s.spec_index(i) == 'z' || s.spec_index(i) == 'Z'))) by {
        if exists|i: int| 0 <= i < s.len() && (s.spec_index(i) == 'z' || s.spec_index(i) == 'Z') {
            let witness_i = choose|i: int| 0 <= i < s.len() && (s.spec_index(i) == 'z' || s.spec_index(i) == 'Z');
            assert(0 <= witness_i < s.len());
            assert(!(s.spec_index(witness_i) == 'z' || s.spec_index(witness_i) == 'Z'));
            assert(false);
        }
    };
    
    false
}

}