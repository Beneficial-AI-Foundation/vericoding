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
                // Prove that the character at position i is '.'
                assert(s_chars[i] == b'.');
                assert(s.spec_index(i as int) == '.');
                assert(s.len() - (i as int) - 1 == 2);
                return true;
            }
        }
        i += 1;
    }
    
    // At this point, we've checked all positions and found no decimal with 2 precision
    assert(i == s_chars.len());
    assert(s_chars.len() == s.len());
    assert(forall|j: int| 0 <= j < s.len() ==> !(s.spec_index(j) == '.' && s.len() - j - 1 == 2));
    return false;
}

}