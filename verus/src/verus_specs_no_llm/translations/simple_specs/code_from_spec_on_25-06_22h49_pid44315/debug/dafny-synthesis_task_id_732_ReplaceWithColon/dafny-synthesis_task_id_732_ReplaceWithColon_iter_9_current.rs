use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsSpaceCommaDot(c: char) -> bool {
    c == ' ' || c == ',' || c == '.'
}

// Helper function to convert a single character
fn convert_char(c: char) -> (result: char)
    ensures
        result == if IsSpaceCommaDot(c) { ':' } else { c }
{
    if c == ' ' || c == ',' || c == '.' {
        ':'
    } else {
        c
    }
}

fn ReplaceWithColon(s: String) -> (v: String)
    ensures
        v.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> (IsSpaceCommaDot(s@.index(i)) ==> v@.index(i) == ':') && (!IsSpaceCommaDot(s@.index(i)) ==> v@.index(i) == s@.index(i))
{
    let ghost original_s = s@;
    let mut result = String::with_capacity(s.len());
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            result.len() == i,
            s@ == original_s,
            forall|j: int| 0 <= j < i ==> (IsSpaceCommaDot(original_s.index(j)) ==> result@.index(j) == ':') && (!IsSpaceCommaDot(original_s.index(j)) ==> result@.index(j) == original_s.index(j))
    {
        let c = s.get_char(i);
        let new_char = convert_char(c);
        result.push(new_char);
        
        proof {
            assert(s@.index(i as int) == c);
            assert(new_char == if IsSpaceCommaDot(c) { ':' } else { c });
            assert(result@.index(i as int) == new_char);
            
            if IsSpaceCommaDot(c) {
                assert(result@.index(i as int) == ':');
            } else {
                assert(result@.index(i as int) == c);
                assert(result@.index(i as int) == original_s.index(i as int));
            }
        }
        
        i += 1;
    }
    
    proof {
        assert(result.len() == s.len());
        assert(forall|k: int| 0 <= k < s.len() ==> 
            (IsSpaceCommaDot(original_s.index(k)) ==> result@.index(k) == ':') && 
            (!IsSpaceCommaDot(original_s.index(k)) ==> result@.index(k) == original_s.index(k)));
    }
    
    result
}

}