use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ToCharArray(s: Seq<char>) -> (a: Vec<char>)
    requires
        s.len() <= usize::MAX
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
            idx <= s_len,
            s.len() <= usize::MAX
    {
        let ch = s[idx as int];
        a.push(ch);
        
        proof {
            let old_idx = idx;
            assert(a.len() == old_idx + 1);
            assert(a.spec_index(old_idx as int) == s.spec_index(old_idx as int));
            assert(forall|i: int| 0 <= i < old_idx ==> a.spec_index(i) == s.spec_index(i));
            assert(forall|i: int| 0 <= i < old_idx + 1 ==> a.spec_index(i) == s.spec_index(i));
        }
        
        idx = idx + 1;
    }
    
    a
}

}