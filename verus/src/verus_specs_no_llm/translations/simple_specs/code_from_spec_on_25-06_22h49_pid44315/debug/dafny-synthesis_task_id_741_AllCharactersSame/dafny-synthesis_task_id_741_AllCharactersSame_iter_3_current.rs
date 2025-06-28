use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn AllCharactersSame(s: String) -> (result: bool)
    ensures
        result ==> forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s.spec_index(i) == s.spec_index(j),
        !result ==> (s.len() > 1) && (exists|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && s.spec_index(i) != s.spec_index(j))
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
            forall|k: int| 0 <= k < i ==> s.spec_index(k) == s.spec_index(0),
            first_char == s_bytes[0],
            first_char == s.spec_index(0),
    {
        if s_bytes[i] != first_char {
            assert(s_bytes[i] == s.spec_index(i as int)) by {
                assert(s_bytes@ == s@);
                assert(0 <= i < s_bytes.len());
            };
            assert(first_char == s.spec_index(0));
            assert(s.spec_index(0 as int) != s.spec_index(i as int));
            assert(0 as int != i as int);
            assert(0 <= 0 < s.len() && 0 <= i < s.len());
            return false;
        }
        
        assert(s_bytes[i] == s.spec_index(i as int)) by {
            assert(s_bytes@ == s@);
            assert(0 <= i < s_bytes.len());
        };
        assert(s_bytes[i] == first_char);
        assert(s.spec_index(i as int) == s.spec_index(0));
        
        i += 1;
    }
    
    assert(i == s_bytes.len());
    assert(s_bytes.len() == s.len());
    assert(forall|k: int| 0 <= k < s.len() ==> s.spec_index(k) == s.spec_index(0));
    
    // Prove the postcondition for result == true
    assert(forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s.spec_index(i) == s.spec_index(j)) by {
        assert(forall|k: int| 0 <= k < s.len() ==> s.spec_index(k) == s.spec_index(0));
    };
    
    return true;
}

}