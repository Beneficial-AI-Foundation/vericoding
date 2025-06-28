use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MaxDifference(a: Vec<int>) -> (diff: int)
    requires
        a.len() > 1
    ensures
        forall|i, j| 0 <= i < a.len() && 0 <= j < a.len() ==> a.spec_index(i) - a.spec_index(j) <= diff
{
    let mut max_val = a[0];
    let mut min_val = a[0];
    let mut idx: usize = 1;
    
    while idx < a.len()
        invariant
            1 <= idx <= a.len(),
            forall|k: int| 0 <= k < idx ==> a.spec_index(k) <= max_val,
            forall|k: int| 0 <= k < idx ==> min_val <= a.spec_index(k),
            exists|k: int| 0 <= k < idx && a.spec_index(k) == max_val,
            exists|k: int| 0 <= k < idx && a.spec_index(k) == min_val,
        decreases a.len() - idx
    {
        let current_val = a[idx];
        if current_val > max_val {
            max_val = current_val;
        }
        if current_val < min_val {
            min_val = current_val;
        }
        idx = idx + 1;
    }
    
    let diff = max_val - min_val;
    
    // Prove the postcondition
    assert(forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> 
        a.spec_index(i) - a.spec_index(j) <= diff) by {
        assert(forall|k: int| 0 <= k < a.len() ==> a.spec_index(k) <= max_val);
        assert(forall|k: int| 0 <= k < a.len() ==> min_val <= a.spec_index(k));
    };
    
    diff
}

}

Key fixes made:


The verification should now pass because:
- The loop invariants correctly maintain that `max_val` is at least as large as any element processed and `min_val` is at most as small as any element processed
- After the loop, these properties hold for all elements in the array
- The postcondition follows logically: for any two indices `i, j`, `a[i] - a[j] <= max_val - min_val = diff`