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
    let mut max_idx = 0;
    let mut i = 1;
    
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            0 <= max_idx < i,
            max_val == a.spec_index(max_idx),
            forall|k: int| 0 <= k < i ==> max_val >= a.spec_index(k)
    {
        if (a[i] as int) > max_val {
            max_val = a[i] as int;
            max_idx = i;
        }
        i = i + 1;
    }
    
    proof {
        // At this point i == a.len(), so we've examined all elements
        assert(i == a.len());
        assert(0 <= max_idx < a.len());
        
        // The invariant gives us that max_val >= all elements from 0 to i-1 = a.len()-1
        assert(forall|k: int| 0 <= k < a.len() ==> max_val >= a.spec_index(k));
        
        // The invariant also gives us that max_val equals the element at max_idx
        assert(max_val == a.spec_index(max_idx));
        assert(exists|j: int| 0 <= j < a.len() && max_val == a.spec_index(j));
    }
    
    max_val
}

}