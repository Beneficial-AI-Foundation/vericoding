use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

exec fn findMin(a: Vec<f64>, from: nat, to: nat) -> (index: nat)
    requires 
        0 <= from < to <= a.len()
    ensures 
        from <= index < to,
        forall|k: nat| from <= k < to ==> a[k as int] <= a[index as int]
{
    let mut min_index = from;
    let mut i = from + 1;
    
    while i < to
        invariant
            from <= min_index < to,
            from + 1 <= i <= to,
            forall|k: nat| from <= k < i ==> a[k as int] <= a[min_index as int]
    {
        if a[i as int] < a[min_index as int] {
            min_index = i;
        }
        i = i + 1;
    }
    
    min_index
}

// Proof function to help with verification
proof fn lemma_findMin_correctness(a: Vec<f64>, from: nat, to: nat, min_index: nat, final_i: nat)
    requires
        0 <= from < to <= a.len(),
        from <= min_index < to,
        final_i == to,
        forall|k: nat| from <= k < final_i ==> a[k as int] <= a[min_index as int]
    ensures
        forall|k: nat| from <= k < to ==> a[k as int] <= a[min_index as int]
{
    // This proof is automatic given the preconditions
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
    let from = 0nat;
    let to = 5nat;
    
    // We specify that there exists an index that satisfies the minimum property
    exists|index: nat| 
        from <= index < to &&
        forall|k: nat| from <= k < to ==> a[k as int] <= a[index as int]
}

}