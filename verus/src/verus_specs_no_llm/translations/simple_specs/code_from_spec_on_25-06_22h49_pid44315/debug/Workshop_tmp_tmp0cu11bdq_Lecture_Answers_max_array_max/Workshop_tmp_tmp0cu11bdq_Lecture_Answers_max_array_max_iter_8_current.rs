use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn max(a: Vec<int>) -> (max: int)
    requires
        a.len() > 0
    ensures
        forall|j: int| 0 <= j < a.len() ==> max >= a.spec_index(j),
        exists|j: int| 0 <= j < a.len() && max == a.spec_index(j)
{
    let mut max_val = a[0];
    let mut i: usize = 1;
    
    while i < a.len()
        invariant
            i >= 1 && i <= a.len(),
            exists|k: int| 0 <= k < i && max_val == a.spec_index(k),
            forall|j: int| 0 <= j < i ==> max_val >= a.spec_index(j)
    {
        if a[i] > max_val {
            max_val = a[i];
        }
        i += 1;
    }
    
    // Add proof annotation to help establish the postcondition
    assert(i == a.len());
    assert(forall|j: int| 0 <= j < a.len() ==> max_val >= a.spec_index(j));
    assert(exists|k: int| 0 <= k < a.len() && max_val == a.spec_index(k));
    
    max_val
}

}