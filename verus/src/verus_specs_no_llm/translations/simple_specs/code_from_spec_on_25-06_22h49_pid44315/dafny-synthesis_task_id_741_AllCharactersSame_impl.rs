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
    
    let first_char = s@.get_char(0);
    let mut i: usize = 1;
    
    while i < s.len()
        invariant
            1 <= i <= s.len(),
            s.len() > 1,
            forall|k: int| 0 <= k < i ==> s@.get_char(k) == first_char,
    {
        let current_char = s@.get_char(i as int);
        if current_char != first_char {
            // We found two different characters
            assert(s@.get_char(i as int) != s@.get_char(0));
            assert(0 <= 0 < s.len() && 0 <= i as int < s.len());
            assert(0 != i as int);
            
            assert(exists|x: int, y: int| 0 <= x < s.len() && 0 <= y < s.len() && x != y && s@.get_char(x) != s@.get_char(y)) by {
                // Provide witnesses for the existential
                let witness_x = 0int;
                let witness_y = i as int;
                assert(0 <= witness_x < s.len());
                assert(0 <= witness_y < s.len());
                assert(witness_x != witness_y);
                assert(s@.get_char(witness_x) != s@.get_char(witness_y));
            };
            return false;
        }
        
        i += 1;
    }
    
    assert(i == s.len());
    assert(forall|k: int| 0 <= k < s.len() ==> s@.get_char(k) == first_char);
    
    // Prove the postcondition for result == true
    assert(forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s@.get_char(i) == s@.get_char(j)) by {
        // For any two indices i, j in bounds, both characters equal first_char, so they're equal
        assert(forall|x: int, y: int| 0 <= x < s.len() && 0 <= y < s.len() ==> {
            &&& s@.get_char(x) == first_char
            &&& s@.get_char(y) == first_char
            &&& s@.get_char(x) == s@.get_char(y)
        });
    };
    
    return true;
}

}