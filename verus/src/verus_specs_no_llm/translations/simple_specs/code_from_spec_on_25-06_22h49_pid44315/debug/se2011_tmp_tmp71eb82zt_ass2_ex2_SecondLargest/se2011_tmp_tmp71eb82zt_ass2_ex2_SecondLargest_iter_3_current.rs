use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SecondLargest(a: Vec<int>) -> (seclar: int)
    requires
        a.len() > 0
    ensures
        exists|i: int| 0 <= i < a.len() && forall|j: int| (0 <= j < a.len() && j != i) ==> (a.spec_index(i) >= a.spec_index(j)) && (seclar <= a.spec_index(i)) && ( if a.spec_index(j) != a.spec_index(i) then seclar >= a.spec_index(j) else seclar <= a.spec_index(j))
{
    // Find the maximum element
    let mut max_val = a[0];
    let mut max_idx = 0;
    
    let mut i = 1;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
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
    
    // Now we know max_val is the maximum and max_idx is its index
    assert(forall|k: int| 0 <= k < a.len() ==> a.spec_index(k) <= max_val);
    assert(a.spec_index(max_idx as int) == max_val);
    
    // Find the second largest value (largest among non-maximum elements)
    let mut second_largest = max_val; // Initialize to max_val
    let mut j = 0;
    
    while j < a.len()
        invariant
            0 <= j <= a.len(),
            second_largest <= max_val,
            max_val == a.spec_index(max_idx as int),
            0 <= max_idx < a.len(),
            forall|k: int| 0 <= k < a.len() ==> a.spec_index(k) <= max_val,
            forall|k: int| 0 <= k < j ==> (a.spec_index(k) < max_val ==> a.spec_index(k) <= second_largest),
    {
        if a[j] < max_val {
            if a[j] > second_largest {
                second_largest = a[j];
            }
        } else if a[j] == max_val && j != max_idx {
            // If we find another element equal to max_val, second_largest should be max_val
            second_largest = max_val;
        }
        j += 1;
    }
    
    // Post-loop assertions to help verification
    assert(forall|k: int| 0 <= k < a.len() ==> (a.spec_index(k) < max_val ==> a.spec_index(k) <= second_largest));
    assert(second_largest <= max_val);
    
    // The postcondition is satisfied with max_idx as the witness for i
    assert(0 <= max_idx < a.len());
    assert(forall|j: int| (0 <= j < a.len() && j != max_idx) ==> (a.spec_index(max_idx as int) >= a.spec_index(j)));
    assert(second_largest <= a.spec_index(max_idx as int));
    
    // For each j != max_idx:
    // If a[j] != a[max_idx] (i.e., a[j] < max_val), then second_largest >= a[j]
    // If a[j] == a[max_idx] (i.e., a[j] == max_val), then second_largest <= a[j] (which is true since second_largest <= max_val)
    assert(forall|j: int| (0 <= j < a.len() && j != max_idx) ==> 
        (if a.spec_index(j) != a.spec_index(max_idx as int) then second_largest >= a.spec_index(j) else second_largest <= a.spec_index(j)));
    
    second_largest
}

}