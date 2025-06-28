use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Minimum(a: Vec<int>) -> (m: int)
    requires
        a.len() > 0
    ensures
        exists|i: int| 0 <= i < a.len() && m == a[i],
        forall|i: int| 0 <= i < a.len() ==> m <= a[i]
{
    let mut min = a[0];
    let mut idx: usize = 1;
    
    while idx < a.len()
        invariant
            1 <= idx <= a.len(),
            exists|i: int| 0 <= i < idx && min == a[i],
            forall|i: int| 0 <= i < idx ==> min <= a[i]
    {
        if a[idx as int] < min {
            min = a[idx as int];
        }
        idx = idx + 1;
    }
    
    assert(idx == a.len());
    assert(exists|i: int| 0 <= i < a.len() && min == a[i]);
    assert(forall|i: int| 0 <= i < a.len() ==> min <= a[i]);
    
    min
}

}