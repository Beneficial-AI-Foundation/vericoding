// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn as_array_spec(a: Vec<f32>) -> Seq<f32> {
    a@
}

proof fn as_array_preserves_properties(a: Vec<f32>)
    ensures
        a@.len() == a.len(),
        forall|i: int| 0 <= i < a@.len() ==> a@[i] == a[i]
{
    assert(a@.len() == a.len());
    assert(forall|i: int| 0 <= i < a@.len() ==> a@[i] == a[i]);
}
// </vc-helpers>

// <vc-spec>
fn asarray(a: Vec<f32>) -> (result: Vec<f32>)
    requires a.len() > 0,
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i]
// </vc-spec>
// <vc-code>
{
    proof {
        as_array_preserves_properties(a);
    }
    a
}
// </vc-code>

}
fn main() {}