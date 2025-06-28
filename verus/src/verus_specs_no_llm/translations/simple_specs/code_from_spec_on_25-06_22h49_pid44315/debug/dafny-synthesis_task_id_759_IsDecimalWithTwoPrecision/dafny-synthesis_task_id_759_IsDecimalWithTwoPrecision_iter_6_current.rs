use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsDecimalWithTwoPrecision(s: String) -> (result: bool)
    ensures
        result ==> (exists|i: int| 0 <= i < s.len() && s.spec_index(i) == '.' && s.len() - i - 1 == 2),
        !result ==> !(exists|i: int| 0 <= i < s.len() && s.spec_index(i) == '.' && s.len() - i - 1 == 2)
{
    // Check if string is ASCII first - this simplifies the byte/char correspondence
    if !s.is_ascii() {
        return false;
    }
    
    let s_chars = s.as_bytes();
    let mut i: usize = 0;
    
    while i < s_chars.len()
        invariant
            0 <= i <= s_chars.len(),
            s_chars.len() == s.len(),
            s_chars@ == s@.as_bytes(),
            s.is_ascii(),
            // For ASCII strings, byte position equals character position
            forall|j: int| 0 <= j < i ==> !(s_chars[j] == b'.' && s_chars.len() - j - 1 == 2),
            forall|j: int| 0 <= j < i ==> !(s.spec_index(j) == '.' && s.len() - j - 1 == 2)
    {
        if s_chars[i] == b'.' {
            if s_chars.len() - i - 1 == 2 {
                // For ASCII strings, byte position corresponds to character position
                assert(s.is_ascii());
                assert(s_chars[i] == b'.');
                assert(s.spec_index(i as int) == '.');
                assert(s.len() - (i as int) - 1 == 2);
                assert(0 <= i < s.len());
                return true;
            }
        }
        i += 1;
    }
    
    // We've checked all positions and didn't find a decimal with two precision
    assert(i == s_chars.len());
    assert(s_chars.len() == s.len());
    assert(forall|j: int| 0 <= j < s.len() ==> !(s_chars[j as usize] == b'.' && s_chars.len() - j - 1 == 2));
    
    // For ASCII strings, this implies the character-level property
    assert(s.is_ascii());
    assert(forall|j: int| 0 <= j < s.len() ==> !(s.spec_index(j) == '.' && s.len() - j - 1 == 2));
    
    return false;
}

}