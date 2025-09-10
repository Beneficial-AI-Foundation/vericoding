use vstd::prelude::*;

verus! {

fn M(N: i32, a: &[i32]) -> (result: (i32, i32))
    requires 
        0 <= N,
        a.len() == N,
        (forall|k: int| 0 <= k && k < N ==> 0 <= a[k]),
    ensures 
        result.0 <= N * result.1,
{
    assume(false);
    unreached()
}

}
fn main() {}