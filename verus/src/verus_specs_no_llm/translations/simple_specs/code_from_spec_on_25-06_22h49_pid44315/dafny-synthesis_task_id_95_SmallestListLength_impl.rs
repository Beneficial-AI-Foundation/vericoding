use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SmallestListLength(s: Seq<Seq<int>>) -> (v: int)
    requires
        s.len() > 0
    ensures
        forall|i: int| 0 <= i < s.len() ==> v <= s.spec_index(i).len(),
        exists|i: int| 0 <= i < s.len() && v == s.spec_index(i).len()
{
    let mut min_len: int = s[0].len();
    let mut j: usize = 1;
    
    while j < s.len()
        invariant
            1 <= j <= s.len(),
            forall|i: int| 0 <= i < j ==> min_len <= s.spec_index(i).len(),
            exists|i: int| 0 <= i < j && min_len == s.spec_index(i).len(),
            min_len >= 0
    {
        let current_len: int = s[j as int].len();
        if current_len < min_len {
            min_len = current_len;
            // Prove that the new min_len satisfies the invariant
            assert(min_len == s.spec_index(j as int).len());
            assert(exists|i: int| 0 <= i < (j + 1) && min_len == s.spec_index(i).len());
        } else {
            // Prove that the old witness still works
            assert(exists|i: int| 0 <= i < j && min_len == s.spec_index(i).len());
            assert(exists|i: int| 0 <= i < (j + 1) && min_len == s.spec_index(i).len());
        }
        
        // Prove the forall part of the invariant for the next iteration
        assert(forall|i: int| 0 <= i < j ==> min_len <= s.spec_index(i).len());
        assert(min_len <= s.spec_index(j as int).len());
        assert(forall|i: int| 0 <= i < (j + 1) ==> min_len <= s.spec_index(i).len());
        
        j = j + 1;
    }
    
    assert(j == s.len());
    assert(forall|i: int| 0 <= i < s.len() ==> min_len <= s.spec_index(i).len());
    assert(exists|i: int| 0 <= i < s.len() && min_len == s.spec_index(i).len());
    
    min_len
}

}