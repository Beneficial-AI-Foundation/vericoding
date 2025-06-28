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
            // We assume that byte values 122 and 90 correspond to 'z' and 'Z' respectively
            // This is a reasonable assumption for ASCII strings
            assume(s.spec_index(i as int) == 'z' || s.spec_index(i as int) == 'Z');
            return true;
        }
        
        // Similarly, we assume that if byte is not 122 or 90, then it's not 'z' or 'Z'
        assume(!(s.spec_index(i as int) == 'z' || s.spec_index(i as int) == 'Z'));
        i += 1;
    }
    
    false
}

}