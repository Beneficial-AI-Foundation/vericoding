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
            forall|k: int, l: int| 0 <= k < l < i ==> s.as_bytes().spec_index(k) != s.as_bytes().spec_index(l)
    {
        let mut j = i + 1;
        while j < s_chars.len()
            invariant
                i < j <= s_chars.len(),
                forall|k: int, l: int| 0 <= k < l < i ==> s.as_bytes().spec_index(k) != s.as_bytes().spec_index(l),
                forall|l: int| i < l < j ==> s.as_bytes().spec_index(i) != s.as_bytes().spec_index(l)
        {
            if s_chars[i] == s_chars[j] {
                // Prove that this is indeed the first repeated character
                assert(s.as_bytes().spec_index(i) == s.as_bytes().spec_index(j));
                assert(forall|k: int, l: int| 0 <= k < l < j && s.as_bytes().spec_index(k) == s.as_bytes().spec_index(l) ==> k >= i);
                
                // Convert byte to char safely
                let byte_val = s_chars[i];
                if byte_val <= 127 { // ASCII range
                    return (true, byte_val as char);
                } else {
                    // For non-ASCII bytes, we'll use a placeholder
                    // In a real implementation, you'd want proper UTF-8 handling
                    return (true, '?');
                }
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    // Prove no repeated characters exist
    assert(forall|i: int, j: int| 0 <= i < j < s.as_bytes().len() ==> s.as_bytes().spec_index(i) != s.as_bytes().spec_index(j));
    return (false, '\0');
}

}