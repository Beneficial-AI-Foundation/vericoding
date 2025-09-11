// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn M(N: i32, a: &[i32]) -> (result: (i32, i32))
    requires 
        0 <= N,
        a.len() == N,
        (forall|k: int| 0 <= k && k < N ==> 0 <= a[k]),
    ensures 
        result.0 <= N * result.1,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}