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
    let s_chars = s.as_bytes();
    let mut i: usize = 0;
    
    while i < s_chars.len()
        invariant
            0 <= i <= s_chars.len(),
            s_chars.len() == s.len(),
            forall|j: int| 0 <= j < i ==> !(s.spec_index(j) == '.' && s.len() - j - 1 == 2)
    {
        if s_chars[i] == b'.' {
            if s_chars.len() - i - 1 == 2 {
                // We found a dot at position i with exactly 2 characters after it
                // We need to prove that s.spec_index(i as int) == '.'
                // Since s_chars[i] == b'.' and s is valid UTF-8 (String guarantee),
                // we know that the character at position i in the string is '.'
                proof {
                    // The byte b'.' corresponds to the char '.'
                    assert(s_chars[i] == b'.');
                    // For ASCII characters like '.', the byte and char representations align
                    assert(s.spec_index(i as int) == '.');
                }
                return true;
            }
        }
        i += 1;
    }
    
    // At this point, we've checked all positions and found no decimal with 2 precision
    proof {
        assert(i == s_chars.len());
        assert(s_chars.len() == s.len());
        // From the loop invariant, we know no position 0..i has the property
        // Since i == s.len(), no position in the entire string has the property
        assert(forall|j: int| 0 <= j < s.len() ==> !(s.spec_index(j) == '.' && s.len() - j - 1 == 2));
    }
    return false;
}

}