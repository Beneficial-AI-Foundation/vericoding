// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn np_isclose(a: Vec<i32>, b: Vec<i32>, tol: i32) -> (result: Vec<bool>)
    requires 
        a.len() > 0,
        a.len() == b.len(),
        tol > 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> 
            result[i] == (-tol < a[i] - b[i] && a[i] - b[i] < tol),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}