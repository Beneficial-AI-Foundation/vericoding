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
            m == a[max_index as int] as int,
            forall|k: int| 0 <= k < i ==> m >= a[k as int]
    {
        if a[i] as int > m {
            m = a[i] as int;
            max_index = i;
        }
        i = i + 1;
    }
    
    assert(0 <= max_index < a.len());
    assert(m == a[max_index as int] as int);
    assert(forall|k: int| 0 <= k < a.len() ==> m >= a[k as int]);
    
    m
}

// Specification method to demonstrate the properties
spec fn checker_spec(a: Vec<nat>, m: int) -> bool {
    &&& (a.len() > 0 ==> (forall|k: int| 0 <= k < a.len() ==> m >= a[k as int]))
    &&& (a.len() == 0 ==> m == -1)
    &&& (a.len() > 0 ==> exists|i: int| 0 <= i < a.len() && m == a[i as int])
}

// Test function to verify the Max function works correctly
fn test_max() {
    let empty_vec: Vec<nat> = Vec::new();
    let result1 = Max(empty_vec);
    assert(result1 == -1);
    
    let mut single_vec: Vec<nat> = Vec::new();
    single_vec.push(5);
    let result2 = Max(single_vec);
    assert(result2 == 5);
    
    proof {
        assert(checker_spec(Vec::new(), -1));
    }
}

}