use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn FindMax(a: Vec<int>) -> (max: int)
    requires
        a.len() > 0
    ensures
        0 <= max < a.len(),
        forall|x: int| 0 <= x < a.len() ==> a.spec_index(max) >= a.spec_index(x)
{
    let mut max_idx = 0;
    let mut i = 1;
    
    while i < a.len()
        invariant
            0 <= max_idx < a.len(),
            1 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a.spec_index(max_idx) >= a.spec_index(j)
    {
        if a[i] > a[max_idx] {
            max_idx = i;
        }
        i = i + 1;
    }
    
    max_idx
}

}