use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn mmaximum1(v: Vec<int>) -> (i: int)
    requires
        v.len() > 0
    ensures
        0 <= i < v.len(),
        forall |k: int| 0 <= k < v.len() ==> v.spec_index(i) >= v.spec_index(k)
{
    let mut max_idx: usize = 0;
    let mut idx: usize = 1;
    
    while idx < v.len()
        invariant
            0 <= max_idx < v.len(),
            1 <= idx <= v.len(),
            forall |k: int| 0 <= k < idx ==> v.spec_index(max_idx as int) >= v.spec_index(k)
    {
        if v.spec_index(idx as int) > v.spec_index(max_idx as int) {
            max_idx = idx;
        }
        idx += 1;
    }
    
    // After the loop, idx == v.len()
    assert(idx == v.len());
    
    // The loop invariant gives us what we need for the postcondition
    assert(forall |k: int| 0 <= k < idx ==> v.spec_index(max_idx as int) >= v.spec_index(k));
    
    // Since idx == v.len(), we can substitute
    assert(forall |k: int| 0 <= k < v.len() ==> v.spec_index(max_idx as int) >= v.spec_index(k));
    
    // We need to ensure max_idx is still in bounds
    assert(0 <= max_idx < v.len());
    
    // Ensure the conversion is safe
    assert(max_idx < v.len());
    assert(0 <= max_idx as int < v.len());
    
    max_idx as int
}

}