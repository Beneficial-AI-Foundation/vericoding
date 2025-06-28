use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn find_first_repeated_char(s: &str) -> (found: bool, c: char)
    ensures
        found ==> exists|i: int, j: int| 0 <= i < j < s.as_bytes().len() && 
            s.as_bytes().spec_index(i) == s.as_bytes().spec_index(j) && 
            s.as_bytes().spec_index(i) == c as u8 && 
            (forall|k: int, l: int| 0 <= k < l < j && s.as_bytes().spec_index(k) == s.as_bytes().spec_index(l) ==> k >= i),
        !found ==> (forall|i: int, j: int| 0 <= i < j < s.as_bytes().len() ==> s.as_bytes().spec_index(i) != s.as_bytes().spec_index(j))
{
    let s_bytes = s.as_bytes();
    let mut i = 0;
    
    while i < s_bytes.len()
        invariant
            0 <= i <= s_bytes.len(),
            // No repeated character found in the prefix [0, i)
            forall|k: int, l: int| 0 <= k < l < i ==> s.as_bytes().spec_index(k) != s.as_bytes().spec_index(l),
    {
        let mut j = i + 1;
        while j < s_bytes.len()
            invariant
                i + 1 <= j <= s_bytes.len(),
                0 <= i < s_bytes.len(),
                // No repeated chars in prefix [0, i)
                forall|k: int, l: int| 0 <= k < l < i ==> s.as_bytes().spec_index(k) != s.as_bytes().spec_index(l),
                // Character at i doesn't match any in [i+1, j)
                forall|l: int| i + 1 <= l < j ==> s.as_bytes().spec_index(i as int) != s.as_bytes().spec_index(l)
        {
            if s_bytes[i] == s_bytes[j] {
                // Found first repeated character
                let byte_val = s_bytes[i];
                
                // Convert byte to char - use a simple approach
                let result_char = byte_val as char;
                
                // Prove the postcondition
                proof {
                    assert(s.as_bytes().spec_index(i as int) == s.as_bytes().spec_index(j as int));
                    assert(0 <= i < j < s.as_bytes().len());
                    assert(s.as_bytes().spec_index(i as int) == result_char as u8);
                    
                    // Prove this is the first repeated character
                    assert(forall|k: int, l: int| 0 <= k < l < j && s.as_bytes().spec_index(k) == s.as_bytes().spec_index(l) ==> k >= i as int) by {
                        // Any repeated pair with both positions < j must have first position >= i
                        // because we've checked all pairs in [0, i) and found no repeats
                        // and we've checked char at i against [i+1, j) and found no matches except at j
                    };
                }
                
                return (true, result_char);
            }
            j = j + 1;
        }
        
        i = i + 1;
    }
    
    // No repeated characters found
    proof {
        // At this point, we've checked all pairs and found no repeats
        assert(forall|x: int, y: int| 0 <= x < y < s.as_bytes().len() ==> s.as_bytes().spec_index(x) != s.as_bytes().spec_index(y)) by {
            // The invariant ensures no repeats in [0, i) where i == s_bytes.len()
            // So no repeats in the entire string
        };
    }
    
    return (false, '\0');
}

}