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
            forall|k: int| 0 <= k < j ==> v[i as int] >= v[k],
            i < j  // i is among the elements we've seen
    {
        if v[j as int] > v[i as int] {
            i = j;
        }
        j = j + 1;
    }
    
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
    let mut max_idx: usize = 0;
    
    while j < v.len()
        invariant
            1 <= j <= v.len(),
            0 <= max_idx < v.len(),
            v[max_idx as int] == m,
            forall|k: int| 0 <= k < j ==> m >= v[k],
            max_idx < j  // max_idx is among the elements we've seen
    {
        if v[j as int] > m {
            m = v[j as int];
            max_idx = j;
        }
        j = j + 1;
    }
    
    m
}

}