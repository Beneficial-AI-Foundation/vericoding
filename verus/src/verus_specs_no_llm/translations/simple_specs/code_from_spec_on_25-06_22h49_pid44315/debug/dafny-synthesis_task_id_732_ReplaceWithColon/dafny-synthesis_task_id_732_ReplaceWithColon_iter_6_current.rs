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
        forall|i: int| 0 <= i < s.len() ==> (IsSpaceCommaDot(s@.index(i)) ==> v@.index(i) == ':') && (!IsSpaceCommaDot(s@.index(i)) ==> v@.index(i) == s@.index(i))
{
    let ghost s_seq = s@;
    let mut result = String::new();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            result.len() == i,
            s@ == s_seq,
            forall|j: int| 0 <= j < i ==> (IsSpaceCommaDot(s_seq.index(j)) ==> result@.index(j) == ':') && (!IsSpaceCommaDot(s_seq.index(j)) ==> result@.index(j) == s_seq.index(j))
    {
        let c = s.chars().nth(i).unwrap();
        
        if IsSpaceCommaDot(c) {
            result.push(':');
        } else {
            result.push(c);
        }
        
        proof {
            assert(s_seq.index(i as int) == c);
            assert(result@.index(i as int) == if IsSpaceCommaDot(c) { ':' } else { c });
            
            // Maintain the invariant for the next iteration
            assert(forall|j: int| 0 <= j < (i + 1) ==> 
                (IsSpaceCommaDot(s_seq.index(j)) ==> result@.index(j) == ':') && 
                (!IsSpaceCommaDot(s_seq.index(j)) ==> result@.index(j) == s_seq.index(j)));
        }
        
        i += 1;
    }
    
    proof {
        assert(result.len() == s.len());
        assert(s@ == s_seq);
        assert(forall|k: int| 0 <= k < s.len() ==> 
            (IsSpaceCommaDot(s_seq.index(k)) ==> result@.index(k) == ':') && 
            (!IsSpaceCommaDot(s_seq.index(k)) ==> result@.index(k) == s_seq.index(k)));
    }
    
    result
}

}