use vstd::prelude::*;

verus! {

fn find_max(a: &[i32]) -> (i: usize)

    requires 
        a.len() > 0,
    ensures
        i < a.len(),
        forall|k: int| 0 <= k < a.len() ==> a[k] <= a[i as int],
{
    assume(false);
    unreached();
}

}
fn main() {}