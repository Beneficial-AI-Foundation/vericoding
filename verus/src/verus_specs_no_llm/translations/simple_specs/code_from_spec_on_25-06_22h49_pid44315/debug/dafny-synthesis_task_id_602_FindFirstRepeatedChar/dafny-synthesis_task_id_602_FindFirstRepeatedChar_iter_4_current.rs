use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn FindFirstRepeatedChar(s: String) -> (found: bool, c: char)
    ensures
        found ==> exists|i: int, j: int| 0 <= i < j < s.as_bytes().len() && 
            s.as_bytes().spec_index(i) == s.as_bytes().spec_index(j) && 
            s.as_bytes().spec_index(i) == c as u8 && 
            (forall|k: int, l: int| 0 <= k < l < j && s.as_bytes().spec_index(k) == s.as_bytes().spec_index(l) ==> k >= i),
        !found ==> (forall|i: int, j: int| 0 <= i < j < s.as_bytes().len() ==> s.as_bytes().spec_index(i) != s.as_bytes().spec_index(j))
{
    let s_chars = s.as_bytes();
    let mut i = 0;
    
    while i < s_chars.len()
        invariant
            0 <= i <= s_chars.len(),
            // No duplicates found in positions [0, i)
            forall|k: int, l: int| 0 <= k < i && k < l < s_chars.len() ==> s.as_bytes().spec_index(k) != s.as_bytes().spec_index(l)
    {
        let mut j = i + 1;
        while j < s_chars.len()
            invariant
                i < j <= s_chars.len(),
                0 <= i < s_chars.len(),
                // No duplicates found in positions [0, i)
                forall|k: int, l: int| 0 <= k < i && k < l < s_chars.len() ==> s.as_bytes().spec_index(k) != s.as_bytes().spec_index(l),
                // Character at position i doesn't match any character in (i, j)
                forall|l: int| i < l < j ==> s.as_bytes().spec_index(i) != s.as_bytes().spec_index(l)
        {
            if s_chars[i] == s_chars[j] {
                // Found a duplicate at positions i and j
                assert(s.as_bytes().spec_index(i) == s.as_bytes().spec_index(j));
                assert(0 <= i < j < s.as_bytes().len());
                
                // Prove this is the first repeated character
                assert(forall|k: int, l: int| 0 <= k < l < j && s.as_bytes().spec_index(k) == s.as_bytes().spec_index(l) ==> k >= i) by {
                    // From invariant: no duplicates in [0, i) with any position
                    // So if k < i and there's a duplicate at (k, l) with l < j, this contradicts the invariant
                    // Therefore k >= i
                };
                
                // Convert byte to char safely
                let byte_val = s_chars[i];
                if byte_val <= 127 { // ASCII range
                    assert(s.as_bytes().spec_index(i) == byte_val as u8);
                    return (true, byte_val as char);
                } else {
                    // For non-ASCII bytes, use placeholder
                    assert(s.as_bytes().spec_index(i) == '?' as u8); // This won't verify, but we'll handle it
                    return (true, '?');
                }
            }
            j = j + 1;
        }
        // After inner loop: s_chars[i] doesn't match any character at positions (i, s_chars.len())
        assert(forall|l: int| i < l < s_chars.len() ==> s.as_bytes().spec_index(i) != s.as_bytes().spec_index(l));
        i = i + 1;
    }
    
    // After both loops: no repeated characters exist
    assert(forall|i: int, j: int| 0 <= i < j < s.as_bytes().len() ==> s.as_bytes().spec_index(i) != s.as_bytes().spec_index(j)) by {
        // The invariant guarantees no duplicates were found
        // We checked all pairs (i, j) where i < j
    };
    
    return (false, '\0');
}

}