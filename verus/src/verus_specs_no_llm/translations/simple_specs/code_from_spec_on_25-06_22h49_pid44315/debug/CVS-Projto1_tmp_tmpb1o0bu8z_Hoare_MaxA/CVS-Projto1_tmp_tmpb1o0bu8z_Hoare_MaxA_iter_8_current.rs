use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MaxA(a: Vec<int>) -> (m: int)
    requires
        a.len() > 0
    ensures
        forall|i: int| 0 <= i < a.len() ==> a.spec_index(i) <= m,
        exists|i: int| 0 <= i < a.len() && a.spec_index(i) == m
{
    let mut max = a[0];
    let mut idx: usize = 1;
    
    while idx < a.len()
        invariant
            1 <= idx <= a.len(),
            forall|i: int| 0 <= i < idx ==> a.spec_index(i) <= max,
            exists|i: int| 0 <= i < idx && a.spec_index(i) == max
    {
        assert(idx < a.len());
        let current = a[idx as int];
        if current > max {
            max = current;
        }
        idx += 1;
    }
    
    max
}

}