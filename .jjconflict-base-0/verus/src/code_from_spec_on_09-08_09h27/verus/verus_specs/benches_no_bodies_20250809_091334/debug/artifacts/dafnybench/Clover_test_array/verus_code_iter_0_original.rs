use vstd::prelude::*;

verus! {
    fn test_array_elements(a: &mut Vec<i32>, j: usize)
        requires 
            0 <= j < old(a).len(),
        ensures 
            a[j as int] == 60,
            forall|k: int| 0 <= k < old(a).len() && k != j ==> a[k] == old(a)[k],
    {
    // TODO: Remove this comment and implement the function body
    }
}

fn main() {}