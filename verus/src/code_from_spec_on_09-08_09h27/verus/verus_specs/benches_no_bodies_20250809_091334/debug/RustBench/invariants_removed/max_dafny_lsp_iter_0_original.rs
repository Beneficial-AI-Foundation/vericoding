use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn max(a: &[i32]) -> (x: usize)
    requires
        a.len() > 0,
    ensures
        0 <= x < a.len(),
        forall|k: int| 0 <= k < a.len() ==> a[k] <= a[x as int],
{
    return 0;  // TODO: Remove this line and implement the function body
}

fn main() {}
}
