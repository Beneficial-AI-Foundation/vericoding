use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SecondLargest(a: Vec<int>) -> (seclar: int)
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
    
    // Now find the second largest (which could be equal to max if all elements are the same)
    let mut second_largest = a[0];
    let mut j = 0usize;
    
    while j < a.len()
        invariant
            0 <= j <= a.len(),
            max_val == a.spec_index(max_idx as int),
            0 <= max_idx < a.len(),
            forall|k: int| 0 <= k < a.len() ==> a.spec_index(k) <= max_val,
            second_largest <= max_val,
            exists|idx: int| 0 <= idx < a.len() && a.spec_index(idx) == second_largest,
            forall|k: int| 0 <= k < j ==> a.spec_index(k) <= second_largest,
    {
        if a[j] > second_largest {
            second_largest = a[j];
        }
        j += 1;
    }
    
    // Prove the postcondition
    assert(second_largest <= max_val);
    assert(forall|k: int| 0 <= k < a.len() ==> a.spec_index(k) <= second_largest);
    assert(exists|k: int| 0 <= k < a.len() && a.spec_index(k) == second_largest);
    
    second_largest
}

}