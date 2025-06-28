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
        forall|i: int| 0 <= i < v.len() ==> s1@.contains(v@.index(i)) && !s2@.contains(v@.index(i)),
        forall|j: int| 0 <= j < s1.len() ==> s2@.contains(s1@.index(j)) || v@.contains(s1@.index(j))
{
    let mut result = String::new();
    let mut i: usize = 0;
    
    while i < s1.len()
        invariant
            0 <= i <= s1.len(),
            result.len() <= i,
            forall|k: int| 0 <= k < result.len() ==> s1@.contains(result@.index(k)) && !s2@.contains(result@.index(k)),
            forall|j: int| 0 <= j < i ==> s2@.contains(s1@.index(j)) || result@.contains(s1@.index(j))
    {
        let ch = s1@.index(i as int);
        
        let mut found_in_s2 = false;
        let mut j: usize = 0;
        
        // Check if ch is in s2
        while j < s2.len()
            invariant
                0 <= j <= s2.len(),
                found_in_s2 ==> s2@.contains(ch),
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
            assert(!s2@.contains(ch));
        }
        if found_in_s2 {
            assert(s2@.contains(ch));
        }
        
        if !found_in_s2 {
            assert(!s2@.contains(ch));
            assert(s1@.contains(ch)) by {
                assert(s1@.index(i as int) == ch);
                assert(0 <= i < s1.len());
            }
            let old_result_len = result.len();
            result.push(ch);
            assert(result@.index(old_result_len as int) == ch);
            assert(result@.contains(ch));
            
            // Prove that the new character satisfies the invariant conditions
            assert(s1@.contains(result@.index(old_result_len as int)) && !s2@.contains(result@.index(old_result_len as int)));
        } else {
            assert(s2@.contains(ch));
        }
        
        // Help prove the invariant for the next iteration
        assert(forall|j: int| 0 <= j < (i + 1) ==> s2@.contains(s1@.index(j)) || result@.contains(s1@.index(j))) by {
            assert(forall|j: int| 0 <= j < i ==> s2@.contains(s1@.index(j)) || result@.contains(s1@.index(j)));
            assert(s2@.contains(s1@.index(i as int)) || result@.contains(s1@.index(i as int)));
        }
        
        i += 1;
    }
    
    // Final assertions to help prove postconditions
    assert(i == s1.len());
    assert(forall|j: int| 0 <= j < s1.len() ==> s2@.contains(s1@.index(j)) || result@.contains(s1@.index(j)));
    
    result
}

}