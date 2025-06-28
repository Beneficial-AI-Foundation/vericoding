use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn second_largest(a: Vec<int>) -> (seclar: int)
    requires
        a.len() > 0
    ensures
        // There exists a largest element, and seclar is the largest among all elements 
        // that are smaller than or equal to the largest
        exists|max_idx: int| 0 <= max_idx < a.len() && 
            (forall|j: int| 0 <= j < a.len() ==> a.spec_index(j) <= a.spec_index(max_idx)) &&
            (forall|j: int| 0 <= j < a.len() ==> a.spec_index(j) <= seclar) &&
            (seclar <= a.spec_index(max_idx)) &&
            (exists|k: int| 0 <= k < a.len() && a.spec_index(k) == seclar)
{
    // Find the maximum element
    let mut max_val = a[0];
    let mut max_idx = 0usize;
    
    let mut i = 1usize;
    while i < a.len()
        invariant
            0 < i <= a.len(),
            0 <= max_idx < i,
            max_val == a.spec_index(max_idx as int),
            forall|k: int| 0 <= k < i ==> a.spec_index(k) <= max_val,
    {
        if a[i] > max_val {
            max_val = a[i];
            max_idx = i;
        }
        i += 1;
    }
    
    // Now max_val is the maximum element in the array
    assert(forall|k: int| 0 <= k < a.len() ==> a.spec_index(k) <= max_val);
    
    // The postcondition actually allows returning the maximum element itself
    // since it asks for the largest among all elements that are <= the largest
    // This means we can return max_val, which satisfies all conditions
    
    // Prove that max_val satisfies all the postconditions
    assert(exists|max_idx_witness: int| 0 <= max_idx_witness < a.len() && 
        (forall|j: int| 0 <= j < a.len() ==> a.spec_index(j) <= a.spec_index(max_idx_witness)) &&
        (forall|j: int| 0 <= j < a.len() ==> a.spec_index(j) <= max_val) &&
        (max_val <= a.spec_index(max_idx_witness)) &&
        (exists|k: int| 0 <= k < a.len() && a.spec_index(k) == max_val)) by {
        
        // Use max_idx as the witness for max_idx_witness
        assert(0 <= max_idx as int < a.len());
        assert(max_val == a.spec_index(max_idx as int));
        assert(forall|j: int| 0 <= j < a.len() ==> a.spec_index(j) <= a.spec_index(max_idx as int));
        assert(forall|j: int| 0 <= j < a.len() ==> a.spec_index(j) <= max_val);
        assert(max_val <= a.spec_index(max_idx as int));
        assert(a.spec_index(max_idx as int) == max_val);
    }
    
    max_val
}

}