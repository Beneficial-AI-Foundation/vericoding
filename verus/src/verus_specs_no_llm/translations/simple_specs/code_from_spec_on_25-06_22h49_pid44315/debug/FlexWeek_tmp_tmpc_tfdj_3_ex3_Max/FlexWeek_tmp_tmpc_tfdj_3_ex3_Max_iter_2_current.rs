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
    let mut i = 1;
    
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            max_val >= 0,
            forall|k: int| 0 <= k < i ==> max_val >= a.spec_index(k),
            exists|j: int| 0 <= j < i && max_val == a.spec_index(j),
            max_val == a.spec_index(0) || exists|j: int| 1 <= j < i && max_val == a.spec_index(j)
    {
        if (a[i] as int) > max_val {
            max_val = a[i] as int;
        }
        i = i + 1;
    }
    
    // At this point, we need to prove the postconditions
    assert(forall|k: int| 0 <= k < a.len() ==> max_val >= a.spec_index(k));
    assert(exists|j: int| 0 <= j < a.len() && max_val == a.spec_index(j));
    
    max_val
}

}