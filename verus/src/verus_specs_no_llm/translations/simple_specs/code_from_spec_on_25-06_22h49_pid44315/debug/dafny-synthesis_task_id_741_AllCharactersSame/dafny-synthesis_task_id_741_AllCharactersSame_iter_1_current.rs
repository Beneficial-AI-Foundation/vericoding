use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn AllCharactersSame(s: String) -> (result: bool)
    ensures
        result ==> forall i, j :: 0 <= i < s.len() && 0 <= j < s.len() ==> s.spec_index(i) == s.spec_index(j),
        !result ==> (s.len() > 1) && (exists i, j :: 0 <= i < s.len() && 0 <= j < s.len() && i != j && s.spec_index(i) != s.spec_index(j))
{
    if s.len() <= 1 {
        return true;
    }
    
    let first_char = s.spec_index(0);
    let mut i = 1;
    
    while i < s.len()
        invariant
            1 <= i <= s.len(),
            forall k :: 0 <= k < i ==> s.spec_index(k) == first_char,
    {
        if s.spec_index(i) != first_char {
            assert(s.spec_index(0) != s.spec_index(i));
            assert(0 != i);
            return false;
        }
        i += 1;
    }
    
    assert(forall k :: 0 <= k < s.len() ==> s.spec_index(k) == first_char);
    return true;
}

}