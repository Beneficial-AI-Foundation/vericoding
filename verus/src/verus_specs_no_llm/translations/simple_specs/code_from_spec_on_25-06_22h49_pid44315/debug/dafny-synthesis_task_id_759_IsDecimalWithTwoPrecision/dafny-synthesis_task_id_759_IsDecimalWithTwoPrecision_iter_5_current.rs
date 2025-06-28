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
            s_chars@ == s@.as_bytes(),
            forall|j: int| 0 <= j < i ==> !(s_chars[j] == b'.' && s_chars.len() - j - 1 == 2),
            forall|j: int| 0 <= j < i ==> !(s.spec_index(j) == '.' && s.len() - j - 1 == 2)
    {
        if s_chars[i] == b'.' {
            if s_chars.len() - i - 1 == 2 {
                // We found a dot at position i with exactly 2 characters after it
                // Since we're working with bytes and the dot character '.' is ASCII,
                // the byte position corresponds to the character position
                assert(s.spec_index(i as int) == '.');
                assert(s.len() - (i as int) - 1 == 2);
                return true;
            }
        }
        i += 1;
    }
    
    // We've checked all positions and didn't find a decimal with two precision
    assert(forall|j: int| 0 <= j < s.len() ==> !(s.spec_index(j) == '.' && s.len() - j - 1 == 2));
    return false;
}

}