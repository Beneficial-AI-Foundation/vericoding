use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Max(a: Vec<nat>) -> (m: int)
    ensures 
        a.len() > 0 ==> (forall|k: int| 0 <= k < a.len() ==> m >= a[k]),
        a.len() == 0 ==> m == -1,
        a.len() > 0 ==> exists|i: int| 0 <= i < a.len() && m == a[i]
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
            forall|k: int| 0 <= k < i ==> m >= a[k] as int
        decreases a.len() - i
    {
        if (a[i] as int) > m {
            m = a[i] as int;
            max_index = i;
        }
        i = i + 1;
    }
    
    // Final assertions to help verification
    assert(i == a.len());
    assert(0 <= max_index < a.len());
    assert(m == a[max_index] as int);
    
    // Prove the first postcondition
    assert(forall|k: int| 0 <= k < a.len() ==> m >= a[k] as int) by {
        assert(forall|k: int| 0 <= k < i ==> m >= a[k] as int);
        assert(i == a.len());
    }
    
    // Since nat can be cast to int, we need to show m >= a[k] (not a[k] as int)
    assert(forall|k: int| 0 <= k < a.len() ==> m >= a[k]) by {
        assert(forall|k: int| 0 <= k < a.len() ==> m >= a[k] as int);
        // For any nat n, n as int >= n
        assert(forall|k: int| 0 <= k < a.len() ==> a[k] as int >= a[k]);
    }
    
    // Prove the third postcondition
    assert(exists|j: int| 0 <= j < a.len() && m == a[j]) by {
        assert(0 <= max_index < a.len());
        assert(m == a[max_index] as int);
        // Since a[max_index] is nat and m is int, and m == a[max_index] as int
        // We need to show that m == a[max_index]
        // This is true because for nat n, if m == n as int, then m == n (when m >= 0)
        assert(a[max_index] >= 0); // nat is non-negative
        assert(m >= 0); // m is max of non-negative values
        assert(m == a[max_index]);
    }
    
    m
}

// Specification method to demonstrate the properties
spec fn checker_spec(a: Vec<nat>, m: int) -> bool {
    &&& (a.len() > 0 ==> (forall|k: int| 0 <= k < a.len() ==> m >= a[k]))
    &&& (a.len() == 0 ==> m == -1)
    &&& (a.len() > 0 ==> exists|i: int| 0 <= i < a.len() && m == a[i])
}

}