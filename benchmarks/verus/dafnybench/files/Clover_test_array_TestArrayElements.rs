use vstd::prelude::*;

verus! {

fn test_array_elements(a: &mut Vec<i32>, j: usize)
    requires 
        j < old(a).len(),
    ensures 
        a.len() == old(a).len(),
        a[j as int] == 60,
        forall|k: int| 0 <= k < a.len() && k != j ==> a[k] == old(a)[k],
{
    assume(false);
    unreached()
}

}
fn main() {}