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
            idx <= s.len()
    {
        let ch = s[idx as int];
        a.push(ch);
        
        proof {
            // Help Verus understand that the newly pushed element matches
            assert(a.len() == idx + 1);
            assert(a.spec_index(idx as int) == s.spec_index(idx as int));
            
            // Maintain the invariant for all previous elements
            assert(forall|i: int| 0 <= i < idx ==> a.spec_index(i) == s.spec_index(i));
            assert(forall|i: int| 0 <= i < idx + 1 ==> a.spec_index(i) == s.spec_index(i));
        }
        
        idx = idx + 1;
    }
    
    proof {
        // Final assertion to help with postcondition
        assert(idx == s_len);
        assert(a.len() == s.len());
        assert(forall|i: int| 0 <= i < s.len() ==> a.spec_index(i) == s.spec_index(i));
    }
    
    a
}

}