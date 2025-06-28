use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn AllCharactersSame(s: &str) -> (result: bool)
    ensures
        result ==> forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s@.get_char(i) == s@.get_char(j),
        !result ==> (s.len() > 1) && (exists|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && s@.get_char(i) != s@.get_char(j))
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
            s_bytes@ =~= s@.as_bytes(),
            forall|k: int| 0 <= k < i ==> s_bytes@[k] == first_char,
            first_char == s_bytes@[0],
            s.len() > 1,
    {
        if s_bytes[i] != first_char {
            // We found two different characters
            assert(s_bytes@[i as int] != s_bytes@[0]);
            assert(s@.as_bytes()[i as int] != s@.as_bytes()[0]);
            assert(0 <= 0 < s.len() && 0 <= i < s.len());
            assert(0 != i as int);
            
            // The different bytes imply different characters
            assert(s@.get_char(0) != s@.get_char(i as int));
            
            assert(exists|x: int, y: int| 0 <= x < s.len() && 0 <= y < s.len() && x != y && s@.get_char(x) != s@.get_char(y)) by {
                assert(s@.get_char(0) != s@.get_char(i as int) && 0 != i as int);
            };
            return false;
        }
        
        i += 1;
    }
    
    assert(i == s_bytes.len());
    assert(s_bytes.len() == s.len());
    assert(forall|k: int| 0 <= k < s.len() ==> s_bytes@[k] == first_char);
    
    // Since all bytes are the same and we're dealing with ASCII or single-byte chars,
    // all characters are the same
    assert(forall|k: int| 0 <= k < s.len() ==> s@.get_char(k) == s@.get_char(0));
    
    // Prove the postcondition for result == true
    assert(forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s@.get_char(i) == s@.get_char(j)) by {
        if s.len() > 0 {
            assert(forall|k: int| 0 <= k < s.len() ==> s@.get_char(k) == s@.get_char(0));
            // For any two indices i, j, both s@.get_char(i) and s@.get_char(j) equal s@.get_char(0)
            assert(forall|x: int, y: int| 0 <= x < s.len() && 0 <= y < s.len() ==> {
                s@.get_char(x) == s@.get_char(0) && s@.get_char(y) == s@.get_char(0)
            });
        }
    };
    
    return true;
}

}