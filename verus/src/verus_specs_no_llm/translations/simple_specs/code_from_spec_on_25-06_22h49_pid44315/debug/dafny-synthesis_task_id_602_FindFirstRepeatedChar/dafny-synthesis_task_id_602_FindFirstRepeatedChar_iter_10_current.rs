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
                    assert forall|k: int, l: int| 0 <= k < l < j && s.as_bytes().spec_index(k) == s.as_bytes().spec_index(l) implies k >= i as int by {
                        if k < i as int {
                            // This contradicts our invariant that no repeats exist in [0, i)
                            assert(false);
                        }
                        if k == i as int {
                            // Then l must be in [i+1, j), but our invariant says s_bytes[i] != s_bytes[l] for l in [i+1, j)
                            // except we just found s_bytes[i] == s_bytes[j], so l must be j
                            // But l < j in the premise, contradiction unless this case is impossible
                            if l < j {
                                assert(s.as_bytes().spec_index(i as int) != s.as_bytes().spec_index(l));
                                assert(false);
                            }
                        }
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
        assert forall|x: int, y: int| 0 <= x < y < s.as_bytes().len() implies s.as_bytes().spec_index(x) != s.as_bytes().spec_index(y) by {
            // The final invariant ensures no repeats in [0, i) where i == s_bytes.len()
            // So no repeats in the entire string
        };
    }
    
    return (false, '\0');
}

}