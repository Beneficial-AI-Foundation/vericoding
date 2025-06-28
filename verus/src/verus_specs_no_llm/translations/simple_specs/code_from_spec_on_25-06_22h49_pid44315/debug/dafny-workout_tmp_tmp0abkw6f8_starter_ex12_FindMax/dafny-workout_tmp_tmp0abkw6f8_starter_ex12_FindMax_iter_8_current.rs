use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn FindMax(a: Vec<int>) -> (max_idx: nat)
    requires
        a.len() > 0
    ensures
        0 <= max_idx < a.len(),
        forall|j: int| 0 <= j < a.len() ==> a.spec_index(max_idx as int) >= a.spec_index(j)
{
    let mut max_idx: usize = 0;
    let mut i: usize = 1;
    
    while i < a.len()
        invariant
            0 <= max_idx < a.len(),
            1 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a.spec_index(max_idx as int) >= a.spec_index(j),
            max_idx < i
    {
        if a.spec_index(i as int) > a.spec_index(max_idx as int) {
            max_idx = i;
        }
        i = i + 1;
    }
    
    assert(i == a.len());
    assert(forall|j: int| 0 <= j < i ==> a.spec_index(max_idx as int) >= a.spec_index(j));
    assert(forall|j: int| 0 <= j < a.len() ==> a.spec_index(max_idx as int) >= a.spec_index(j));
    
    max_idx as nat
}

}