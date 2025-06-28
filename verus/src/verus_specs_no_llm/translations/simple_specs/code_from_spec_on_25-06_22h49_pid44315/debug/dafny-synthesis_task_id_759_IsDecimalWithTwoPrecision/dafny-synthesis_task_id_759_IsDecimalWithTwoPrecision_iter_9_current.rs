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
            // No decimal with two precision found so far
            forall|j: int| 0 <= j < i ==> !(s.spec_index(j) == '.' && s.len() - j - 1 == 2)
    {
        if s_chars[i] == b'.' {
            if s_chars.len() - i - 1 == 2 {
                // Found a decimal point with exactly 2 digits after it
                proof {
                    // For ASCII strings, byte b'.' corresponds to char '.'
                    assert(s.is_ascii());
                    assert(s_chars[i] == b'.');
                    // Verus automatically knows that for ASCII strings,
                    // s.spec_index(i) corresponds to the character representation
                    // of the byte s.as_bytes()[i]
                }
                return true;
            }
        }
        
        i += 1;
    }
    
    return false;
}

}