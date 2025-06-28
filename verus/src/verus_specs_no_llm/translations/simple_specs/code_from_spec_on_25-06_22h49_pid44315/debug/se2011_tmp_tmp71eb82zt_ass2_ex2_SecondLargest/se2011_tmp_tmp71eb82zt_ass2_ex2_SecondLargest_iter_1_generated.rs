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
    
    // Now find the second largest (largest element <= max_val)
    let mut second_largest = max_val;
    let mut j = 0;
    
    while j < a.len()
        invariant
            0 <= j <= a.len(),
            second_largest <= max_val,
            forall|k: int| 0 <= k < j ==> (if a.spec_index(k) != max_val then a.spec_index(k) <= second_largest else second_largest <= a.spec_index(k)),
            forall|k: int| 0 <= k < a.len() ==> a.spec_index(k) <= max_val,
            max_val == a.spec_index(max_idx as int),
            forall|k: int| 0 <= k < a.len() && k != max_idx ==> a.spec_index(k) <= max_val,
    {
        if a[j] < max_val && a[j] >= second_largest {
            second_largest = a[j];
        } else if a[j] == max_val && second_largest > max_val {
            second_largest = max_val;
        }
        j += 1;
    }
    
    second_largest
}

}