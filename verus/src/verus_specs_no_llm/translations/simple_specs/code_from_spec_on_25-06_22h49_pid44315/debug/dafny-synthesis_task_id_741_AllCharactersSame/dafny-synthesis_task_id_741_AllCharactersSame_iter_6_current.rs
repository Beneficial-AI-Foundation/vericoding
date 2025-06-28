use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn AllCharactersSame(s: String) -> (result: bool)
    ensures
        result ==> forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s@[i] == s@[j],
        !result ==> (s.len() > 1) && (exists|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && s@[i] != s@[j])
{
    if s.len() <= 1 {
        return true;
    }
    
    let s_bytes = s.as_bytes();
    let first_char = s_bytes[0];
    let mut i: usize = 1;
    
    while i < s_bytes.len()
        invariant
            1 <= i <= s_bytes.len(),
            s_bytes.len() == s.len(),
            s_bytes@ == s@,
            forall|k: int| 0 <= k < i ==> s_bytes[k] == first_char,
            first_char == s_bytes[0],
    {
        if s_bytes[i] != first_char {
            // We found two different characters
            assert(s_bytes[i] != s_bytes[0]);
            assert(s@[i as int] != s@[0]);
            assert(0 <= 0 < s.len() && 0 <= i < s.len());
            assert(0 != i);
            return false;
        }
        
        i += 1;
    }
    
    assert(i == s_bytes.len());
    assert(s_bytes.len() == s.len());
    assert(forall|k: int| 0 <= k < s.len() ==> s_bytes[k] == first_char);
    assert(forall|k: int| 0 <= k < s.len() ==> s@[k] == s@[0]);
    
    // Prove the postcondition for result == true
    assert(forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s@[i] == s@[j]) by {
        if s.len() > 0 {
            assert(forall|k: int| 0 <= k < s.len() ==> s@[k] == s@[0]);
        }
    };
    
    return true;
}

}