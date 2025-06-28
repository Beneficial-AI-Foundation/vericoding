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
                // Prove that we found ch in s2
                assert(char_in_string(ch, s2@)) by {
                    assert(0 <= j < s2@.len() && s2@.index(j as int) == ch);
                }
                break;
            }
            j += 1;
        }
        
        // After the loop, establish the relationship between found_in_s2 and char_in_string
        if !found_in_s2 {
            // If we didn't find it and went through the whole string, it's not there
            assert(j == s2.len());
            assert(forall|k: int| 0 <= k < s2.len() ==> s2@.index(k) != ch);
            assert(!char_in_string(ch, s2@)) by {
                if char_in_string(ch, s2@) {
                    // Use Verus's witness extraction
                    assert(exists|witness_k: int| 0 <= witness_k < s2@.len() && s2@.index(witness_k) == ch);
                    // This leads to a contradiction with our forall statement above
                    assert(false);
                }
            }
        }
        
        if !found_in_s2 {
            // Character is not in s2, so add it to result
            assert(!char_in_string(ch, s2@));
            assert(char_in_string(ch, s1@)) by {
                assert(0 <= i < s1.len() && s1@.index(i as int) == ch);
            }
            
            let old_result = result@;
            let old_len = result.len();
            result.push(ch);
            
            // Prove properties about the updated result
            assert(result@.len() == old_len + 1);
            assert(result@.index(old_len as int) == ch);
            
            // Prove that all characters in the new result satisfy the conditions
            assert(forall|k: int| 0 <= k < result.len() ==> char_in_string(result@.index(k), s1@) && !char_in_string(result@.index(k), s2@)) by {
                // For old characters
                assert(forall|k: int| 0 <= k < old_len ==> result@.index(k) == old_result.index(k));
                assert(forall|k: int| 0 <= k < old_len ==> char_in_string(result@.index(k), s1@) && !char_in_string(result@.index(k), s2@));
                // For the new character
                assert(char_in_string(result@.index(old_len as int), s1@) && !char_in_string(result@.index(old_len as int), s2@));
            }
            
            assert(char_in_string(ch, result@)) by {
                assert(0 <= old_len < result@.len() && result@.index(old_len as int) == ch);
            }
        }
        
        // Prove that the character from s1 is either in s2 or in result
        if found_in_s2 {
            assert(char_in_string(ch, s2@));
        } else {
            assert(char_in_string(ch, result@));
        }
        assert(char_in_string(s1@.index(i as int), s2@) || char_in_string(s1@.index(i as int), result@));
        
        i += 1;
    }
    
    // Final assertions to help prove postconditions
    assert(i == s1.len());
    assert(forall|j: int| 0 <= j < s1.len() ==> char_in_string(s1@.index(j), s2@) || char_in_string(s1@.index(j), result@));
    assert(forall|k: int| 0 <= k < result.len() ==> char_in_string(result@.index(k), s1@) && !char_in_string(result@.index(k), s2@));
    assert(result.len() <= s1.len());
    
    result
}

}