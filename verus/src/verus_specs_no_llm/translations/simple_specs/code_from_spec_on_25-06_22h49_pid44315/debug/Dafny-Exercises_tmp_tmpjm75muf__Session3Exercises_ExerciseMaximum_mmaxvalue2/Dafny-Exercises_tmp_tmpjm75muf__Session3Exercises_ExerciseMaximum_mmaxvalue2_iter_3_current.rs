use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn mmaximum2(v: Vec<int>) -> (i: usize) 
    requires v.len() > 0
    ensures 0 <= i < v.len() 
    ensures forall|k: int| 0 <= k < v.len() ==> v[i as int] >= v[k]
{
    let mut i: usize = 0;
    let mut j: usize = 1;
    
    while j < v.len()
        invariant 
            0 <= i < v.len(),
            1 <= j <= v.len(),
            i < j,
            forall|k: int| 0 <= k < j ==> v[i as int] >= v[k]
    {
        if v[j as int] > v[i as int] {
            i = j;
        }
        j = j + 1;
    }
    
    // Need to prove the postcondition holds
    assert(j == v.len());
    
    // The loop invariant only guarantees the maximum for elements 0..j
    // We need to prove it holds for all elements when j == v.len()
    assert(forall|k: int| 0 <= k < v.len() ==> v[i as int] >= v[k]) by {
        assert(j == v.len());
        // The invariant gives us: forall|k: int| 0 <= k < j ==> v[i as int] >= v[k]
        // Since j == v.len(), this is exactly what we need
    }
    
    i
}

fn mmaxvalue2(v: Vec<int>) -> (m: int)
    requires v.len() > 0
    ensures forall|k: int| 0 <= k < v.len() ==> m >= v[k]
    ensures exists|i: int| 0 <= i < v.len() && m == v[i]
{
    let mut m = v[0];
    let mut j: usize = 1;
    
    while j < v.len()
        invariant
            1 <= j <= v.len(),
            forall|k: int| 0 <= k < j ==> m >= v[k],
            exists|i: int| 0 <= i < j && m == v[i]
    {
        if v[j as int] > m {
            m = v[j as int];
        }
        j = j + 1;
    }
    
    // Need to prove the postconditions hold
    assert(j == v.len());
    
    // Prove the maximum property
    assert(forall|k: int| 0 <= k < v.len() ==> m >= v[k]) by {
        assert(j == v.len());
        // The invariant gives us: forall|k: int| 0 <= k < j ==> m >= v[k]
        // Since j == v.len(), this is exactly what we need
    }
    
    // Prove the existence property
    assert(exists|i: int| 0 <= i < v.len() && m == v[i]) by {
        assert(j == v.len());
        // The invariant gives us: exists|i: int| 0 <= i < j && m == v[i]
        // Since j == v.len(), and the range 0 <= i < j becomes 0 <= i < v.len()
        // We need to be more explicit about this
        assert(exists|i: int| 0 <= i < j && m == v[i]); // from invariant
        // Since j == v.len(), any i with 0 <= i < j also satisfies 0 <= i < v.len()
    }
    
    m
}

}