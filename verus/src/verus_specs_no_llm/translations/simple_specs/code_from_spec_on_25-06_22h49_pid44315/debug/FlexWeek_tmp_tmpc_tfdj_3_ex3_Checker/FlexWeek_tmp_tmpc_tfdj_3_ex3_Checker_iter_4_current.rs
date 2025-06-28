use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Max(a: Vec<nat>) -> (m: int)
    ensures 
        a.len() > 0 ==> (forall|k: int| 0 <= k < a.len() ==> m >= a[k as int]),
        a.len() == 0 ==> m == -1,
        a.len() > 0 ==> exists|i: int| 0 <= i < a.len() && m == a[i as int]
{
    if a.len() == 0 {
        return -1;
    }
    
    let mut m = a[0] as int;
    let mut i = 1;
    let mut max_index = 0;
    
    while i < a.len()
        invariant 
            1 <= i <= a.len(),
            a.len() > 0,
            0 <= max_index < i,
            m == a[max_index] as int,
            forall|k: int| 0 <= k < i ==> m >= a[k as int] as int
        decreases a.len() - i
    {
        if a[i] as int > m {
            m = a[i] as int;
            max_index = i;
        }
        i = i + 1;
    }
    
    assert(0 <= max_index < a.len());
    assert(m == a[max_index] as int);
    assert(forall|k: int| 0 <= k < a.len() ==> m >= a[k as int] as int);
    
    m
}

// Specification method to demonstrate the properties
spec fn checker_spec(a: Vec<nat>, m: int) -> bool {
    &&& (a.len() > 0 ==> (forall|k: int| 0 <= k < a.len() ==> m >= a[k as int]))
    &&& (a.len() == 0 ==> m == -1)
    &&& (a.len() > 0 ==> exists|i: int| 0 <= i < a.len() && m == a[i as int])
}

// Test function with proper spec annotations
fn test_max() {
    // Test empty vector
    let empty_vec: Vec<nat> = vec![];
    let result1 = Max(empty_vec);
    assert(result1 == -1);
    
    // Test single element vector
    let single_vec: Vec<nat> = vec![5nat];
    let result2 = Max(single_vec);
    assert(result2 == 5);
    
    // Test multiple element vector
    let multi_vec: Vec<nat> = vec![1nat, 5nat, 3nat, 2nat];
    let result3 = Max(multi_vec);
    assert(result3 == 5);
}

}