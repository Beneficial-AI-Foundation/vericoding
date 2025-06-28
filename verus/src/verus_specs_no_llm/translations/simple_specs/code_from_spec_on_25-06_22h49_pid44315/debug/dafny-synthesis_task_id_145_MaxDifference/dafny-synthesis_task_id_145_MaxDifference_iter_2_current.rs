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
        if a[idx] > max_val {
            max_val = a[idx];
        }
        if a[idx] < min_val {
            min_val = a[idx];
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
    };
    
    diff
}

}