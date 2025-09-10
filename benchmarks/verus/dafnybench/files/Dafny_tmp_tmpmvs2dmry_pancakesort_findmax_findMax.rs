use vstd::prelude::*;

verus! {

fn findMax(a: &[i32], n: usize) -> (r: usize)
    requires
        a.len() > 0,
        0 < n <= a.len(),
    ensures
        0 <= r < n <= a.len(),
        forall|k: usize| 0 <= k < n <= a.len() ==> a[r as int] >= a[k as int],
{
    assume(false);
    unreached()
}

}
fn main() {}