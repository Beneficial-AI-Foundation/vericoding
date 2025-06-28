use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn StartAndEndWithSameChar(s: &str) -> (result: bool)
    requires
        s.len() > 0
    ensures
        result <==> s.spec_index(0) == s.spec_index(s.len() - 1)
{
    let first_char = s.as_bytes()[0];
    let last_char = s.as_bytes()[s.len() - 1];
    
    // Proof that the bytes comparison corresponds to the spec comparison
    assert(s.as_bytes().len() == s.len());
    assert(s.as_bytes()[0] == s.spec_index(0));
    assert(s.as_bytes()[s.len() - 1] == s.spec_index(s.len() - 1));
    
    first_char == last_char
}

}