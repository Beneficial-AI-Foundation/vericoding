use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn StartAndEndWithSameChar(s: &str) -> (result: bool)
    requires
        s.len() > 0
    ensures
        result <==> s@.index(0) == s@.index(s@.len() - 1)
{
    let bytes = s.as_bytes();
    let first_char = bytes[0];
    let last_char = bytes[bytes.len() - 1];
    
    // Establish the relationship between bytes and string view
    assert(bytes@.len() == s@.len());
    assert(bytes.len() == s.len());
    
    // Prove bounds are valid
    assert(0 < s.len());
    assert(s.len() - 1 < s.len());
    
    // The comparison
    let result = first_char == last_char;
    
    // For the postcondition proof, we need to establish that
    // the byte comparison corresponds to the character comparison
    proof {
        // In Verus, we can rely on the fact that s.as_bytes() preserves
        // the character sequence when accessed by index
        assert(bytes@[0] == s@.index(0));
        assert(bytes@[bytes@.len() - 1] == s@.index(s@.len() - 1));
        assert(result == (s@.index(0) == s@.index(s@.len() - 1)));
    }
    
    result
}

}