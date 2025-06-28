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
        let current_val = a[idx];
        if current_val > max_val {
            max_val = current_val;
        }
        if current_val < min_val {
            min_val = current_val;
        }
        idx = idx + 1;
    }
    
    assert(forall|k| 0 <= k < a.len() ==> a.spec_index(k) <= max_val);
    assert(forall|k| 0 <= k < a.len() ==> min_val <= a.spec_index(k));
    
    let diff = max_val - min_val;
    
    assert(forall|i, j| 0 <= i < a.len() && 0 <= j < a.len() ==> 
        a.spec_index(i) - a.spec_index(j) <= max_val - min_val) by {
        assert(forall|i| 0 <= i < a.len() ==> a.spec_index(i) <= max_val);
        assert(forall|j| 0 <= j < a.len() ==> min_val <= a.spec_index(j));
        assert(forall|i, j| 0 <= i < a.len() && 0 <= j < a.len() ==> {
            let val_i = a.spec_index(i);
            let val_j = a.spec_index(j);
            val_i <= max_val && min_val <= val_j ==> val_i - val_j <= max_val - min_val
        });
    };
    
    diff
}

}