use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn mmaximum1(v: Vec<int>) -> (i: usize) 
    requires 
        v.len() > 0
    ensures 
        0 <= i < v.len(),
        forall|k: int| 0 <= k < v.len() ==> v[i as int] >= v[k]
{
    let mut i: usize = 0;
    let mut j: usize = 1;
    
    while j < v.len()
        invariant
            0 <= i < v.len(),
            1 <= j <= v.len(),
            forall|k: int| 0 <= k < j ==> v[i as int] >= v[k]
    {
        if v[j as int] > v[i as int] {
            i = j;
        }
        j = j + 1;
    }
    
    // After the loop, we need to prove that the invariant implies the postcondition
    assert(j == v.len());
    assert(forall|k: int| 0 <= k < v.len() ==> v[i as int] >= v[k]);
    
    i
}

fn mmaxvalue1(v: &[int]) -> (m: int)
    requires
        v.len() > 0
    ensures
        exists|i: int| 0 <= i < v.len() && v[i] == m,
        forall|k: int| 0 <= k < v.len() ==> m >= v[k]
{
    let mut m = v[0];
    let mut j: usize = 1;
    
    while j < v.len()
        invariant
            1 <= j <= v.len(),
            exists|i: int| 0 <= i < v.len() && v[i] == m,
            forall|k: int| 0 <= k < j ==> m >= v[k]
    {
        if v[j as int] > m {
            m = v[j as int];
        }
        j = j + 1;
    }
    
    // After the loop, we need to prove that the invariant implies the postcondition
    assert(j == v.len());
    assert(forall|k: int| 0 <= k < v.len() ==> m >= v[k]);
    
    m
}

}