// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): identity helper for Vec<i8> */
fn vc_id_vec(a: Vec<i8>) -> (res: Vec<i8>)
    ensures
        res.len() == a.len(),
        forall|i: int| 0 <= i < res.len() ==> res[i] == a[i],
{
    a
}
// </vc-helpers>

// <vc-spec>
fn numpy_flatiter(a: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): call identity helper to return identical vector */
    let result = vc_id_vec(a);
    result
}
// </vc-code>

}
fn main() {}