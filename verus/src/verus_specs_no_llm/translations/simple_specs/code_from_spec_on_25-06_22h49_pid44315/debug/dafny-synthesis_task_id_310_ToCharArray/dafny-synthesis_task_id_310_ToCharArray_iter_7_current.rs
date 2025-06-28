use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ToCharArray(s: Seq<char>) -> (a: Vec<char>)
    ensures
        a.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> a.spec_index(i) == s.spec_index(i)
{
    let mut a = Vec::new();
    let mut idx: usize = 0;
    let s_len = s.len() as usize;
    
    while idx < s_len
        invariant
            a.len() == idx,
            forall|i: int| 0 <= i < idx ==> a.spec_index(i) == s.spec_index(i),
            s_len == s.len(),
            idx <= s.len(),
            0 <= idx <= s.len()
    {
        let ch = s[idx as int];
        a.push(ch);
        
        // Proof annotation to help Verus understand the relationship
        proof {
            assert(a.len() == idx + 1);
            assert(forall|i: int| 0 <= i < idx ==> a.spec_index(i) == s.spec_index(i));
            assert(a.spec_index(idx as int) == ch);
            assert(a.spec_index(idx as int) == s.spec_index(idx as int));
        }
        
        idx = idx + 1;
    }
    
    // Final proof to establish postconditions
    proof {
        assert(idx == s_len);
        assert(a.len() == idx);
        assert(a.len() == s.len());
        assert(forall|i: int| 0 <= i < s.len() ==> a.spec_index(i) == s.spec_index(i));
    }
    
    a
}

}