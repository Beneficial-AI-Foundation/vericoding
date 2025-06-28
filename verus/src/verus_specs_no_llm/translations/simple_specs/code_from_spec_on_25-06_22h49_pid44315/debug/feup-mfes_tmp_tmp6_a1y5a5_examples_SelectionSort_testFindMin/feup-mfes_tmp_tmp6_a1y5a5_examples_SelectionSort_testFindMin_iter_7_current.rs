use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

exec fn findMin(a: Vec<f64>, from: usize, to: usize) -> (index: usize)
    requires 
        0 <= from < to <= a.len()
    ensures 
        from <= index < to,
        forall|k: int| from <= k < to ==> a[index as int] <= a[k]
{
    let mut min_index = from;
    let mut i = from + 1;
    
    while i < to
        invariant
            from <= min_index < to,
            from + 1 <= i <= to,
            forall|k: int| from <= k < i ==> a[min_index as int] <= a[k],
            forall|k: int| from <= k < from + 1 ==> a[min_index as int] <= a[k]
    {
        if a[i] < a[min_index] {
            min_index = i;
        }
        i = i + 1;
    }
    
    // When loop exits, i == to, so we have:
    // forall|k: int| from <= k < to ==> a[min_index as int] <= a[k]
    min_index
}

// Test function
exec fn test_find_min() {
    let mut a: Vec<f64> = Vec::new();
    a.push(3.0);
    a.push(1.0);
    a.push(4.0);
    a.push(1.0);
    a.push(5.0);
    
    let min_idx = findMin(a, 0, 5);
    // The minimum value should be at index 1 or 3 (both have value 1.0)
}

// Spec function for testing properties
spec fn test_find_min_spec() -> bool {
    let a = seq![3.0f64, 1.0f64, 4.0f64, 1.0f64, 5.0f64];
    let from = 0;
    let to = 5;
    
    // We specify that there exists an index that satisfies the minimum property
    (exists|index: int| 
        from <= index < to &&
        (forall|k: int| from <= k < to ==> a[index] <= a[k]))
}

}