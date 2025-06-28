use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Max(a: Vec<nat>) -> (m: int)
    ensures
        a.len() > 0 ==> forall|k: int| 0 <= k < a.len() ==> m >= a.spec_index(k),
        a.len() == 0 ==> m == -1,
        a.len() > 0 ==> exists|i: int| 0 <= i < a.len() && m == a.spec_index(i)
{
    if a.len() == 0 {
        return -1;
    }
    
    let mut max_val = a[0] as int;
    let mut max_idx: usize = 0;
    let mut i: usize = 1;
    
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            0 <= max_idx < a.len(),
            max_val == a.spec_index(max_idx as int),
            forall|k: int| 0 <= k < i ==> max_val >= a.spec_index(k)
    {
        if (a[i] as int) > max_val {
            max_val = a[i] as int;
            max_idx = i;
        }
        i = i + 1;
    }
    
    assert(i == a.len());
    assert(forall|k: int| 0 <= k < a.len() ==> max_val >= a.spec_index(k));
    assert(max_val == a.spec_index(max_idx as int));
    assert(0 <= max_idx < a.len());
    
    max_val
}

}