use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn FindSmallest(s: Vec<int>) -> (min: int)
    requires
        s.len() > 0,
    ensures
        forall|i: int| 0 <= i < s.len() ==> min <= s[i],
        exists|i: int| 0 <= i < s.len() && min == s[i],
{
    let mut min = s[0];
    let mut idx: usize = 1;
    
    while idx < s.len()
        invariant
            1 <= idx <= s.len(),
            forall|i: int| 0 <= i < idx ==> min <= s[i],
            exists|i: int| 0 <= i < idx && min == s[i],
    {
        if s[idx as int] < min {
            min = s[idx as int];
        }
        idx = idx + 1;
    }
    
    min
}

}