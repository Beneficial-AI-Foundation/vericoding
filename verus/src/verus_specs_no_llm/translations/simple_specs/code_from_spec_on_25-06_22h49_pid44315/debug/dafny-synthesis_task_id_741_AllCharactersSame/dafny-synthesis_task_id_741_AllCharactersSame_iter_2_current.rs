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
            forall|k: int| 0 <= k < i ==> s.spec_index(k) == s.spec_index(0),
            first_char == s_bytes[0],
    {
        if s_bytes[i] != first_char {
            assert(s.spec_index(0 as int) != s.spec_index(i as int));
            assert(0 != i);
            return false;
        }
        i += 1;
    }
    
    assert(forall|k: int| 0 <= k < s.len() ==> s.spec_index(k) == s.spec_index(0));
    return true;
}

}