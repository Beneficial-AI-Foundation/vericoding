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
    
    // After the loop, extend the invariants to the entire array
    assert(idx == a.len());
    assert(forall|k: int| 0 <= k < a.len() ==> a.spec_index(k) <= max_val);
    assert(forall|k: int| 0 <= k < a.len() ==> min_val <= a.spec_index(k));
    
    let diff = max_val - min_val;
    
    // Prove the postcondition
    assert(forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> 
        a.spec_index(i) - a.spec_index(j) <= diff) by {
        // For any i, j: a[i] <= max_val and min_val <= a[j]
        // Therefore: a[i] - a[j] <= max_val - min_val = diff
    };
    
    diff
}

}

The key fixes are:



   - Loop maintains bounds for processed elements
   - After loop: `idx == a.len()`, so bounds apply to all elements
   - Postcondition follows: `a[i] - a[j] ≤ max_val - min_val = diff`

This should now verify successfully because Verus can see that the loop invariants, once extended to the full array, directly imply the postcondition.