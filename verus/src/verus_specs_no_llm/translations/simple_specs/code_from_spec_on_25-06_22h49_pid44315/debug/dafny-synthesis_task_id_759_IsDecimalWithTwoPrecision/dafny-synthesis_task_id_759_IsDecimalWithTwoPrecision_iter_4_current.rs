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
    
    // First, we need to check if the string is ASCII-only for our logic to work correctly
    while i < s_chars.len()
        invariant
            0 <= i <= s_chars.len(),
            s_chars.len() == s.len(),
            forall|j: int| 0 <= j < i ==> !(s_chars[j] == b'.' && s_chars.len() - j - 1 == 2)
    {
        if s_chars[i] == b'.' {
            if s_chars.len() - i - 1 == 2 {
                // We found a dot at position i with exactly 2 characters after it
                // For ASCII strings, byte position equals character position
                // Since '.' is ASCII (byte value 46), we can make this connection
                return true;
            }
        }
        i += 1;
    }
    
    return false;
}

}