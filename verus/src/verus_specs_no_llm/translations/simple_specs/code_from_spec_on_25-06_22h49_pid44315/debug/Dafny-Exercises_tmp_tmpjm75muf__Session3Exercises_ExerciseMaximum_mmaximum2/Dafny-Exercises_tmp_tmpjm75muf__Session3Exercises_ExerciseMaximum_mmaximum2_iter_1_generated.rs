use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn mmaximum2(v: Vec<int>) -> (i: int)
    requires
        v.len() > 0
    ensures
        0 <= i < v.len(),
        forall |k: int| 0 <= k < v.len() ==> v.spec_index(i) >= v.spec_index(k)
{
    let mut max_idx: usize = 0;
    let mut idx: usize = 1;
    
    while idx < v.len()
        invariant
            0 <= max_idx < v.len(),
            1 <= idx <= v.len(),
            forall |k: int| 0 <= k < idx ==> v.spec_index(max_idx as int) >= v.spec_index(k)
    {
        if v[idx] > v[max_idx] {
            max_idx = idx;
        }
        idx = idx + 1;
    }
    
    max_idx as int
}

}