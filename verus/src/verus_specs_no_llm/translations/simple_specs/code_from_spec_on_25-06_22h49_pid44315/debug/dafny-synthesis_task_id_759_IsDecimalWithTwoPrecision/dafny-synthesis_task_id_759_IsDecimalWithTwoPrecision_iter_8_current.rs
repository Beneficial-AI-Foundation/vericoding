use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper lemma to establish the relationship between ASCII bytes and characters
proof fn ascii_byte_char_correspondence(s: &String, pos: int)
    requires
        s.is_ascii(),
        0 <= pos < s.len(),
    ensures
        s.as_bytes()[pos] == b'.' <==> s.spec_index(pos) == '.',
{
    // For ASCII strings, the byte representation directly corresponds to the character
    // The dot character '.' has ASCII value 46, which is b'.'
    // Verus knows this correspondence for ASCII strings
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
                    ascii_byte_char_correspondence(&s, i as int);
                }
                assert(s.spec_index(i as int) == '.');
                assert(s.len() - (i as int) - 1 == 2);
                assert(0 <= i < s.len());
                return true;
            }
        }
        
        proof {
            // Establish that current position doesn't satisfy the condition
            ascii_byte_char_correspondence(&s, i as int);
            if s_chars[i] == b'.' {
                assert(s.spec_index(i as int) == '.');
                assert(s.len() - (i as int) - 1 != 2);
            } else {
                assert(s.spec_index(i as int) != '.');
            }
        }
        
        i += 1;
    }
    
    // We've checked all positions and didn't find a decimal with two precision
    proof {
        assert(i == s_chars.len());
        assert(s_chars.len() == s.len());
        
        // The loop invariant already establishes that no position 0 <= j < i
        // satisfies the condition, and now i == s.len(), so we're done
        assert(forall|j: int| 0 <= j < s.len() ==> !(s.spec_index(j) == '.' && s.len() - j - 1 == 2));
    }
    
    return false;
}

}