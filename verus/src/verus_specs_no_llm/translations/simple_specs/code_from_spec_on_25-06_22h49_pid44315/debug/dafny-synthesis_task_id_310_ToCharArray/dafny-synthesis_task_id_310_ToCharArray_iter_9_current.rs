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
            idx <= s_len,
            s.len() <= usize::MAX
    {
        let ch = s[idx as int];
        a.push(ch);
        idx = idx + 1;
        
        proof {
            assert(a.len() == idx);
            assert(forall|i: int| 0 <= i < idx - 1 ==> a.spec_index(i) == s.spec_index(i));
            assert(a.spec_index((idx - 1) as int) == s.spec_index((idx - 1) as int));
        }
    }
    
    proof {
        assert(idx == s_len);
        assert(s_len == s.len());
        assert(a.len() == s.len());
        assert(forall|i: int| 0 <= i < s.len() ==> a.spec_index(i) == s.spec_index(i));
    }
    
    a
}

}