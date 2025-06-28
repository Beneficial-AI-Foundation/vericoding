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
    
    // At this point j == v.len(), so the invariant gives us what we need
    assert(j == v.len());
    assert(forall|k: int| 0 <= k < j ==> v[i as int] >= v[k]);
    
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
    
    // At this point j == v.len(), so the invariant gives us what we need
    assert(j == v.len());
    assert(forall|k: int| 0 <= k < j ==> m >= v[k]);
    
    m
}

}