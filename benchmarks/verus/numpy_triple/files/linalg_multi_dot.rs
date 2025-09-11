// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn multi_dot(A: Vec<Vec<f64>>, B: Vec<Vec<f64>>, C: Vec<Vec<f64>>) -> (result: Vec<Vec<f64>>)
    requires 
        A.len() > 0,
        B.len() > 0, 
        C.len() > 0,
        forall|i: int| 0 <= i < A.len() ==> A[i].len() == B.len(),
        forall|i: int| 0 <= i < B.len() ==> B[i].len() == C.len(),
        forall|i: int| 0 <= i < C.len() ==> C[i].len() > 0,
    ensures
        result.len() == A.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == C[0].len(),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}