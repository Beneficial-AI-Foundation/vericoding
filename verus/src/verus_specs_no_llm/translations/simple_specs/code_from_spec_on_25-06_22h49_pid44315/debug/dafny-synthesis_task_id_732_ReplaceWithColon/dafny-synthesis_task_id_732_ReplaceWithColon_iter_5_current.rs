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
        let c = s@.index(i as int);
        
        if IsSpaceCommaDot(c) {
            result.push(':');
        } else {
            result.push(c);
        }
        
        proof {
            assert(result@.index(i as int) == if IsSpaceCommaDot(c) { ':' } else { c });
            assert(c == s_seq.index(i as int));
        }
        
        i += 1;
    }
    
    proof {
        assert(result.len() == s.len());
        assert(forall|k: int| 0 <= k < s.len() ==> 
            (IsSpaceCommaDot(s_seq.index(k)) ==> result@.index(k) == ':') && 
            (!IsSpaceCommaDot(s_seq.index(k)) ==> result@.index(k) == s_seq.index(k)));
    }
    
    result
}

}