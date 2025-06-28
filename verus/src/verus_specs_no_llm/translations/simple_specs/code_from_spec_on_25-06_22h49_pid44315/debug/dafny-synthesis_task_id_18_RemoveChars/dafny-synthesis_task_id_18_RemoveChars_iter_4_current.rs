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
                break;
            }
            j += 1;
        }
        
        // Establish that found_in_s2 correctly reflects whether ch is in s2
        if j == s2.len() && !found_in_s2 {
            assert(forall|k: int| 0 <= k < s2.len() ==> s2@.index(k) != ch);
            assert(!char_in_string(ch, s2@)) by {
                if char_in_string(ch, s2@) {
                    let witness_i = choose|witness_i: int| 0 <= witness_i < s2@.len() && s2@.index(witness_i) == ch;
                    assert(s2@.index(witness_i) != ch);  // contradiction
                }
            }
        }
        if found_in_s2 {
            assert(char_in_string(ch, s2@)) by {
                assert(exists|k: int| 0 <= k < s2@.len() && s2@.index(k) == ch);
            }
        }
        
        if !found_in_s2 {
            assert(!char_in_string(ch, s2@));
            assert(char_in_string(ch, s1@)) by {
                assert(s1@.index(i as int) == ch);
                assert(0 <= i < s1.len());
            }
            let old_result_len = result.len();
            result.push(ch);
            assert(result@.index(old_result_len as int) == ch);
            assert(char_in_string(ch, result@)) by {
                assert(exists|k: int| 0 <= k < result@.len() && result@.index(k) == ch);
            }
            
            // Prove that the new character satisfies the invariant conditions
            assert(char_in_string(result@.index(old_result_len as int), s1@) && !char_in_string(result@.index(old_result_len as int), s2@));
        } else {
            assert(char_in_string(ch, s2@));
        }
        
        // Help prove the invariant for the next iteration
        assert(forall|j: int| 0 <= j < (i + 1) ==> char_in_string(s1@.index(j), s2@) || char_in_string(s1@.index(j), result@)) by {
            assert(forall|j: int| 0 <= j < i ==> char_in_string(s1@.index(j), s2@) || char_in_string(s1@.index(j), result@));
            assert(char_in_string(s1@.index(i as int), s2@) || char_in_string(s1@.index(i as int), result@));
        }
        
        i += 1;
    }
    
    // Final assertions to help prove postconditions
    assert(i == s1.len());
    assert(forall|j: int| 0 <= j < s1.len() ==> char_in_string(s1@.index(j), s2@) || char_in_string(s1@.index(j), result@));
    
    result
}

}