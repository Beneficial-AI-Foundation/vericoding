use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn lookForMin(a: Vec<int>, i: int) -> (m: int)
    requires
        0 <= i < a.len()
    ensures
        i <= m < a.len(),
        forall|k| i <= k < a.len() ==> a.spec_index(k) >= a.spec_index(m)
{
    let mut min_idx = i as usize;
    let mut j = (i + 1) as usize;
    
    while j < a.len()
        invariant
            0 <= i < a.len(),
            i <= min_idx < a.len(),
            i + 1 <= j <= a.len(),
            forall|k| i <= k < j ==> a.spec_index(k) >= a.spec_index(min_idx as int)
        decreases a.len() - j
    {
        if a.spec_index(j as int) < a.spec_index(min_idx as int) {
            min_idx = j;
        }
        j = j + 1;
    }
    
    // After the loop, j == a.len(), so the invariant covers all elements from i to a.len()-1
    assert(j == a.len());
    assert forall|k| i <= k < a.len() ==> a.spec_index(k) >= a.spec_index(min_idx as int) by {
        if i <= k < a.len() {
            // Since j == a.len() and k < a.len(), we have k < j
            // So the loop invariant applies
            assert(k < j);
        }
    }
    
    min_idx as int
}

}