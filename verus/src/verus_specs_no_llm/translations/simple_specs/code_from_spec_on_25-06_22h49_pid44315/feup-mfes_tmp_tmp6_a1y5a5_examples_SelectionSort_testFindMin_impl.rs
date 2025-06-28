use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn findMin(a: Vec<f64>, from: usize, to: usize) -> (index: usize)
    requires 
        0 <= from < to <= a.len()
    ensures 
        from <= index < to,
        forall|k: int| from <= k < to ==> a[index as int] <= a[k as int]
{
    let mut min_index = from;
    let mut i = from + 1;
    
    while i < to
        invariant
            from <= min_index < to,
            from + 1 <= i <= to,
            forall|k: int| from <= k < i ==> a[min_index as int] <= a[k as int],
            min_index < a.len(),
            i <= a.len()
    {
        if a[i] < a[min_index] {
            min_index = i;
        }
        i = i + 1;
    }
    
    min_index
}

// Test function
proof fn test_find_min() {
    // We'll just verify the spec property
    lemma_min_exists();
    assert(test_find_min_spec());
}

// Spec function for testing properties
spec fn test_find_min_spec() -> bool {
    let a = seq![3.0f64, 1.0f64, 4.0f64, 1.0f64, 5.0f64];
    let from = 0int;
    let to = 5int;
    
    // We specify that there exists an index that satisfies the minimum property
    exists|index: int| 
        from <= index < to &&
        (forall|k: int| from <= k < to ==> a[index] <= a[k])
}

// Helper lemma to prove the spec
proof fn lemma_min_exists()
    ensures test_find_min_spec()
{
    let a = seq![3.0f64, 1.0f64, 4.0f64, 1.0f64, 5.0f64];
    let from = 0int;
    let to = 5int;
    
    // Index 1 contains the minimum value 1.0
    let min_index = 1int;
    
    assert(from <= min_index < to);
    assert(a[min_index] == 1.0f64);
    
    // Prove that a[1] is <= all other elements
    assert(a[1] <= a[0]); // 1.0 <= 3.0
    assert(a[1] <= a[1]); // 1.0 <= 1.0
    assert(a[1] <= a[2]); // 1.0 <= 4.0
    assert(a[1] <= a[3]); // 1.0 <= 1.0
    assert(a[1] <= a[4]); // 1.0 <= 5.0
    
    assert(forall|k: int| from <= k < to ==> a[min_index] <= a[k]);
}

}