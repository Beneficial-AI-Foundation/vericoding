use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
fn find_first_repeated_char(s: &str) -> (result: (bool, char))
    ensures 
        (result.0 ==> exists|i: int, j: int| 0 <= i < j < s@.len() && s@[i] == s@[j] && s@[i] == result.1 && 
            (forall|k: int, l: int| 0 <= k < l < j && s@[k] == s@[l] ==> k >= i)) &&
        (!result.0 ==> (forall|i: int, j: int| 0 <= i < j < s@.len() ==> s@[i] != s@[j]))
// </vc-spec>
// <vc-code>
{
    let mut seen: Set<char> = Set::empty();
    let mut i: usize = 0;
    
    while i < s@.len()
        invariant
            0 <= i <= s@.len(),
            forall|k: int, l: int| 0 <= k < l < i ==> s@[k] != s@[l],
            forall|k: int| 0 <= k < i ==> seen.contains(s@[k]),
            forall|c: char| seen.contains(c) ==> exists|k: int| 0 <= k < i && s@[k] == c,
    {
        let c = s@[i];
        
        if seen.contains(c) {
            // Found first repeated character
            proof {
                assert(exists|j: int| 0 <= j < i && s@[j] == c);
            }
            
            // Find the first occurrence of this character
            let mut first_idx: usize = 0;
            while first_idx < i
                invariant
                    0 <= first_idx <= i,
                    forall|k: int| 0 <= k < first_idx ==> s@[k] != c,
            {
                if s@[first_idx] == c {
                    break;
                }
                first_idx = first_idx + 1;
            }
            
            proof {
                assert(s@[first_idx] == c);
                assert(forall|k: int| 0 <= k < first_idx ==> s@[k] != c);
                assert(first_idx < i && s@[i] == c);
                
                // Prove this is the first repeated character
                assert forall|k: int, l: int| 0 <= k < l < i + 1 && s@[k] == s@[l] implies k >= first_idx by {
                    if k < l && l < i + 1 && s@[k] == s@[l] {
                        if l == i {
                            assert(s@[l] == c);
                            assert(s@[k] == c);
                            if k < first_idx {
                                assert(s@[k] != c);
                                assert(false);
                            }
                        } else {
                            assert(l < i);
                            assert(forall|k: int, l: int| 0 <= k < l < i ==> s@[k] != s@[l]);
                            assert(s@[k] != s@[l]);
                            assert(false);
                        }
                    }
                }
            }
            
            return (true, c);
        }
        
        seen = seen.insert(c);
        i = i + 1;
    }
    
    // No repeated character found
    proof {
        assert(forall|k: int, l: int| 0 <= k < l < s@.len() ==> s@[k] != s@[l]);
    }
    (false, 'a')
}
// </vc-code>

fn main() {}

}