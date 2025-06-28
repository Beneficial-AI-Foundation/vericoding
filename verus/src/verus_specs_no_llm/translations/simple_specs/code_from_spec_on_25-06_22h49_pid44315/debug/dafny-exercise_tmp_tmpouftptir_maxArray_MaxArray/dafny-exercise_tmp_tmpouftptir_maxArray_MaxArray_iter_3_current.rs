use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MaxArray(a: Vec<int>) -> (max: int)
    requires
        a.len() > 0
    ensures
        forall|i: int| 0 <= i < a.len() ==> a.spec_index(i) <= max,
        exists|i: int| 0 <= i < a.len() && a.spec_index(i) == max
{
    let mut max = a[0];
    let mut j: usize = 1;
    
    while j < a.len()
        invariant
            0 < j <= a.len(),
            forall|k: int| 0 <= k < j ==> a.spec_index(k) <= max,
            exists|k: int| 0 <= k < j && a.spec_index(k) == max
    {
        if a[j] > max {
            max = a[j];
        }
        j = j + 1;
    }
    
    // After the loop, j == a.len(), so the invariant gives us what we need for the postcondition
    assert(j == a.len());
    assert(forall|k: int| 0 <= k < j ==> a.spec_index(k) <= max);
    assert(exists|k: int| 0 <= k < j && a.spec_index(k) == max);
    
    max
}

}