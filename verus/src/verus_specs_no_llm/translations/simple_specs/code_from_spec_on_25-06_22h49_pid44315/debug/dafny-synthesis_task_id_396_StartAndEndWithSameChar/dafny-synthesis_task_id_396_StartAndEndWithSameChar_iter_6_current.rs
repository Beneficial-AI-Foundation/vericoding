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
    
    // Establish that byte indexing corresponds to string indexing
    assert(bytes@[0] == s@.index(0));
    assert(bytes@[bytes@.len() - 1] == s@.index(s@.len() - 1));
    
    // The comparison
    let result = first_char == last_char;
    
    // Prove the postcondition
    assert(result == (first_char == last_char));
    assert(first_char == bytes@[0]);
    assert(last_char == bytes@[bytes@.len() - 1]);
    assert(bytes@[0] == s@.index(0));
    assert(bytes@[bytes@.len() - 1] == s@.index(s@.len() - 1));
    
    result
}

}