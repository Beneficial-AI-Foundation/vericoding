use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn max(a: Vec<int>) -> (max: int)
    requires
        a.len() > 0
    ensures
        forall|j: int| j >= 0 && j < a.len() ==> max >= a.spec_index(j),
        exists|j: int| j >= 0 && j < a.len() && max == a.spec_index(j)
{
    let mut max_val = a[0];
    let mut i = 1;
    
    while i < a.len()
        invariant
            i >= 1 && i <= a.len(),
            max_val == a.spec_index(0) || exists|k: int| 1 <= k < i && max_val == a.spec_index(k),
            forall|j: int| 0 <= j < i ==> max_val >= a.spec_index(j)
    {
        if a[i] > max_val {
            max_val = a[i];
        }
        i += 1;
    }
    
    max_val
}

}