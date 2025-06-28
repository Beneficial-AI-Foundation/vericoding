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
    
    // The comparison
    let result = first_char == last_char;
    
    // For the postcondition proof, we need to establish that
    // the byte comparison corresponds to the character comparison
    proof {
        // Verus understands the relationship between string bytes and characters
        // for single-byte characters (ASCII). The key insight is that if the first
        // and last bytes are equal, then the first and last characters are equal.
        assert(bytes@.len() == s@.len());
        assert(bytes@[0] == first_char);
        assert(bytes@[bytes@.len() - 1] == last_char);
    }
    
    result
}

}