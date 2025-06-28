use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn FindSmallest(s: Vec<int>) -> (min: int)
    requires
        s.len() > 0
    ensures
        forall i: int :: 0 <= i < s.len() ==> min <= s.spec_index(i),
        exists i: int :: 0 <= i < s.len() && min == s.spec_index(i)
{
    let mut min = s[0];
    let mut idx: usize = 1;
    
    while idx < s.len()
        invariant
            1 <= idx <= s.len(),
            forall i: int :: 0 <= i < idx ==> min <= s.spec_index(i),
            exists i: int :: 0 <= i < idx && min == s.spec_index(i)
    {
        if s[idx] < min {
            min = s[idx];
        }
        idx = idx + 1;
    }
    
    min
}

}