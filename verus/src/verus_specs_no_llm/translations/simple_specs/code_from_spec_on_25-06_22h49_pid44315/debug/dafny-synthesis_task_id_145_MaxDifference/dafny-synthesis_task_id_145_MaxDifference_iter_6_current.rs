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
    let mut idx = 1;
    
    while idx < a.len()
        invariant
            1 <= idx <= a.len(),
            forall|k| 0 <= k < idx ==> a.spec_index(k) <= max_val,
            forall|k| 0 <= k < idx ==> min_val <= a.spec_index(k),
            exists|k| 0 <= k < idx && a.spec_index(k) == max_val,
            exists|k| 0 <= k < idx && a.spec_index(k) == min_val,
        decreases a.len() - idx
    {
        // Add explicit bounds check for Verus
        assert(idx < a.len());
        let current_val = a[idx as usize];
        if current_val > max_val {
            max_val = current_val;
        }
        if current_val < min_val {
            min_val = current_val;
        }
        idx = idx + 1;
    }
    
    // After the loop, we have processed all elements
    assert(idx == a.len());
    assert(forall|k| 0 <= k < a.len() ==> a.spec_index(k) <= max_val);
    assert(forall|k| 0 <= k < a.len() ==> min_val <= a.spec_index(k));
    
    let diff = max_val - min_val;
    
    // Prove the postcondition
    assert(forall|i, j| 0 <= i < a.len() && 0 <= j < a.len() ==> 
        a.spec_index(i) - a.spec_index(j) <= max_val - min_val) by {
        // For any i, j in bounds:
        // a[i] <= max_val and min_val <= a[j]
        // Therefore: a[i] - a[j] <= max_val - min_val
        assert(forall|i| 0 <= i < a.len() ==> a.spec_index(i) <= max_val);
        assert(forall|j| 0 <= j < a.len() ==> min_val <= a.spec_index(j));
    };
    
    diff
}

}