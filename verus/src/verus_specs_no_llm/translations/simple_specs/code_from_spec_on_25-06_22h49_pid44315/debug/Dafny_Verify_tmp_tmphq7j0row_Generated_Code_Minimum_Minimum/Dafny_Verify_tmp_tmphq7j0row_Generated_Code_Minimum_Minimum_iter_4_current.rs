use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Minimum(a: Vec<int>) -> (m: int)
    requires
        a.len() > 0
    ensures
        exists i :: 0 <= i < a.len() && m == a.spec_index(i),
        forall i :: 0 <= i < a.len() ==> m <= a.spec_index(i)
{
    let mut min = a[0];
    let mut idx = 1;
    
    while idx < a.len()
        invariant
            1 <= idx <= a.len(),
            exists i :: 0 <= i < a.len() && min == a.spec_index(i),
            forall i :: 0 <= i < idx ==> min <= a.spec_index(i)
    {
        if a[idx] < min {
            min = a[idx];
        }
        idx = idx + 1;
    }
    
    // After the loop, idx == a.len(), so the invariant gives us:
    // forall i :: 0 <= i < a.len() ==> min <= a.spec_index(i)
    // which is exactly what we need for the postcondition
    
    min
}

}