use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsSpaceCommaDot(c: char) -> bool {
    c == ' ' || c == ',' || c == '.'
}

fn ReplaceWithColon(s: String) -> (v: String)
    ensures
        v.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> (IsSpaceCommaDot(s.spec_index(i)) ==> v.spec_index(i) == ':') && (!IsSpaceCommaDot(s.spec_index(i)) ==> v.spec_index(i) == s.spec_index(i))
{
    let mut result = String::new();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> (IsSpaceCommaDot(s.spec_index(j)) ==> result.spec_index(j) == ':') && (!IsSpaceCommaDot(s.spec_index(j)) ==> result.spec_index(j) == s.spec_index(j))
    {
        let c = s.chars().nth(i).unwrap();
        
        // Prove that the character we extracted matches the spec
        assert(c == s.spec_index(i as int));
        
        if IsSpaceCommaDot(c) {
            result.push(':');
            // Prove that we pushed the right character
            assert(result.spec_index(i as int) == ':');
        } else {
            result.push(c);
            // Prove that we pushed the original character
            assert(result.spec_index(i as int) == c);
            assert(result.spec_index(i as int) == s.spec_index(i as int));
        }
        
        // Prove the invariant is maintained
        assert(result.len() == i + 1);
        i += 1;
    }
    
    // Final assertions to help verification
    assert(result.len() == s.len());
    assert(forall|k: int| 0 <= k < s.len() ==> 
        (IsSpaceCommaDot(s.spec_index(k)) ==> result.spec_index(k) == ':') && 
        (!IsSpaceCommaDot(s.spec_index(k)) ==> result.spec_index(k) == s.spec_index(k)));
    
    result
}

}