use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn lookForMin(a: Vec<int>, i: int) -> (m: int)
    requires
        0 <= i < a.len()
    ensures
        i <= m < a.len(),
        forall|k| i <= k < a.len() ==> a.spec_index(k) >= a.spec_index(m)
{
    let mut min_idx = i;
    let mut j = i + 1;
    
    while j < a.len()
        invariant
            i <= min_idx < a.len(),
            i + 1 <= j <= a.len(),
            forall|k| i <= k < j ==> a.spec_index(k) >= a.spec_index(min_idx)
    {
        if a[j] < a[min_idx] {
            min_idx = j;
        }
        j = j + 1;
    }
    
    min_idx
}

}