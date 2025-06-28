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
    let mut min_len = s.spec_index(0).len();
    let mut j = 1;
    
    while j < s.len()
        invariant
            1 <= j <= s.len(),
            forall|i: int| 0 <= i < j ==> min_len <= s.spec_index(i).len(),
            exists|i: int| 0 <= i < j && min_len == s.spec_index(i).len()
    {
        let current_len = s.spec_index(j).len();
        if current_len < min_len {
            min_len = current_len;
        }
        j = j + 1;
    }
    
    min_len
}

}