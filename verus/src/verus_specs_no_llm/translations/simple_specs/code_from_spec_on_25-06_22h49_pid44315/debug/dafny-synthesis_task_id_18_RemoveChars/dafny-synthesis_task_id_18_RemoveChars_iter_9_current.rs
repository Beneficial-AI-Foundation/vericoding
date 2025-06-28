use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn char_in_string(c: char, s: Seq<char>) -> bool {
    exists|i: int| 0 <= i < s.len() && s.index(i) == c
}

fn RemoveChars(s1: String, s2: String) -> (v: String)
    ensures
        v.len() <= s1.len(),
        forall|i: int| 0 <= i < v.len() ==> char_in_string(v@.index(i), s1@) && !char_in_string(v@.index(i), s2@),
        forall|j: int| 0 <= j < s1.len() ==> char_in_string(s1@.index(j), s2@) || char_in_string(s1@.index(j), v@)
{
    let mut result = String::new();
    let mut i: usize = 0;
    
    while i < s1.len()
        invariant
            0 <= i <= s1.len(),
            result.len() <= i,
            forall|k: int| 0 <= k < result.len() ==> char_in_string(result@.index(k), s1@) && !char_in_string(result@.index(k), s2@),
            forall|j: int| 0 <= j < i ==> char_in_string(s1@.index(j), s2@) || char_in_string(s1@.index(j), result@)
    {
        let ch = s1@.index(i as int);
        
        // First establish that ch is in s1
        assert(char_in_string(ch, s1@)) by {
            assert(0 <= i < s1.len() && s1@.index(i as int) == ch);
        }
        
        let mut found_in_s2 = false;
        let mut j: usize = 0;
        
        // Check if ch is in s2
        while j < s2.len()
            invariant
                0 <= j <= s2.len(),
                found_in_s2 ==> char_in_string(ch, s2@),
                !found_in_s2 ==> forall|k: int| 0 <= k < j ==> s2@.index(k) != ch
        {
            if s2@.index(j as int) == ch {
                found_in_s2 = true;
                assert(char_in_string(ch, s2@)) by {
                    assert(0 <= j < s2.len() && s2@.index(j as int) == ch);
                }
                break;
            }
            j += 1;
        }
        
        // Establish the final relationship about ch and s2
        if !found_in_s2 {
            // We've checked all characters in s2 and didn't find ch
            assert(!char_in_string(ch, s2@)) by {
                assert(forall|k: int| 0 <= k < s2.len() ==> s2@.index(k) != ch);
                if char_in_string(ch, s2@) {
                    let witness = choose|witness: int| 0 <= witness < s2.len() && s2@.index(witness) == ch;
                    assert(s2@.index(witness) != ch); // from the forall above
                    assert(s2@.index(witness) == ch);  // from the witness definition
                    assert(false); // contradiction
                }
            }
        }
        
        if !found_in_s2 {
            // Character is not in s2, so add it to result
            let old_result = result@;
            result.push(ch);
            
            // Prove the new character satisfies the conditions
            assert(char_in_string(ch, result@)) by {
                assert(result@.len() == old_result.len() + 1);
                assert(result@.index(old_result.len() as int) == ch);
                assert(0 <= old_result.len() < result@.len());
            }
            
            // Maintain the invariant for all characters in result
            assert(forall|k: int| 0 <= k < result@.len() ==> char_in_string(result@.index(k), s1@) && !char_in_string(result@.index(k), s2@)) by {
                assert(forall|k: int| 0 <= k < old_result.len() ==> result@.index(k) == old_result.index(k));
                assert(result@.index(old_result.len() as int) == ch);
                assert(char_in_string(ch, s1@) && !char_in_string(ch, s2@));
            }
        }
        
        // Maintain the coverage invariant for the next iteration
        assert(forall|j_idx: int| 0 <= j_idx <= i ==> char_in_string(s1@.index(j_idx), s2@) || char_in_string(s1@.index(j_idx), result@)) by {
            let current_char = s1@.index(i as int);
            if found_in_s2 {
                assert(char_in_string(current_char, s2@));
            } else {
                assert(char_in_string(current_char, result@));
            }
        }
        
        i += 1;
    }
    
    // Final assertions to help prove the postconditions
    assert(forall|k: int| 0 <= k < result.len() ==> char_in_string(result@.index(k), s1@) && !char_in_string(result@.index(k), s2@));
    assert(forall|j: int| 0 <= j < s1.len() ==> char_in_string(s1@.index(j), s2@) || char_in_string(s1@.index(j), result@));
    
    result
}

}