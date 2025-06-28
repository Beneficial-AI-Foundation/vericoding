use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn RemoveChars(s1: String, s2: String) -> (v: String)
    ensures
        v.len() <= s1.len(),
        forall|i: int| 0 <= i < v.len() ==> s1@.contains(v@.index(i)) && !s2@.contains(v@.index(i)),
        forall|i: int| 0 <= i < s1.len() ==> s2@.contains(s1@.index(i)) || v@.contains(s1@.index(i))
{
    let mut result = String::new();
    let mut i = 0;
    
    while i < s1.len()
        invariant
            0 <= i <= s1.len(),
            result.len() <= i,
            forall|j: int| 0 <= j < result.len() ==> s1@.contains(result@.index(j)) && !s2@.contains(result@.index(j)),
            forall|j: int| 0 <= j < i ==> s2@.contains(s1@.index(j)) || result@.contains(s1@.index(j))
    {
        let ch = s1.as_bytes()[i] as char;
        
        if !s2.as_str().contains(ch) {
            result.push(ch);
        }
        
        i += 1;
    }
    
    result
}

}