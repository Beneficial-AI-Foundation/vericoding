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
        
        if !found_in_s2 {
            assert(!s2@.contains(ch));
            result.push(ch);
            assert(result@.index((result.len() - 1) as int) == ch);
            assert(s1@.contains(ch));
        } else {
            assert(s2@.contains(ch));
        }
        
        i += 1;
    }
    
    result
}

}