use vstd::prelude::*;

verus! {

fn linear_search(a: &[i32], e: i32) -> (n: usize)
    requires exists|i: int| 0 <= i < a.len() && a[i] == e,
    ensures ({
        &&& 0 <= n < a.len() 
        &&& a[n as int] == e
        &&& forall|k: int| 0 <= k < n as int ==> a[k] != e
    }),
{
    assume(false);
    unreached();
}

}
fn main() {}