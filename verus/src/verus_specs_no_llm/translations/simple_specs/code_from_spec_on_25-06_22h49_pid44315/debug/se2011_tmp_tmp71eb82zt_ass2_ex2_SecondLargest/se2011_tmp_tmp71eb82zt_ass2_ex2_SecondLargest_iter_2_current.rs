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
    
    // Find the second largest value
    let mut second_largest = max_val;
    let mut found_different = false;
    let mut j = 0;
    
    while j < a.len()
        invariant
            0 <= j <= a.len(),
            second_largest <= max_val,
            max_val == a.spec_index(max_idx as int),
            0 <= max_idx < a.len(),
            forall|k: int| 0 <= k < a.len() ==> a.spec_index(k) <= max_val,
            forall|k: int| 0 <= k < j ==> (a.spec_index(k) != max_val ==> a.spec_index(k) <= second_largest),
            found_different ==> (second_largest < max_val && exists|k: int| 0 <= k < j && a.spec_index(k) == second_largest),
    {
        if a[j] < max_val {
            if !found_different || a[j] > second_largest {
                second_largest = a[j];
                found_different = true;
            }
        }
        j += 1;
    }
    
    // If all elements are the same, return that value
    if !found_different {
        second_largest = max_val;
    }
    
    second_largest
}

}