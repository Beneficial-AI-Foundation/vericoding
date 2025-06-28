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
            0 < idx <= a.len(),
            forall|i: int| 0 <= i < idx ==> a.spec_index(i) <= max,
            exists|i: int| 0 <= i < idx && a.spec_index(i) == max
    {
        if a[idx] > max {
            max = a[idx];
        }
        idx += 1;
        
        // Proof that the invariant is maintained
        assert(forall|i: int| 0 <= i < idx ==> a.spec_index(i) <= max);
        assert(exists|i: int| 0 <= i < idx && a.spec_index(i) == max);
    }
    
    // After the loop, idx == a.len(), so the invariant gives us what we need
    assert(forall|i: int| 0 <= i < a.len() ==> a.spec_index(i) <= max);
    assert(exists|i: int| 0 <= i < a.len() && a.spec_index(i) == max);
    
    max
}

}