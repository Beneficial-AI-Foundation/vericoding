// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn id_seq_f32(s: Seq<f32>) -> Seq<f32> { s }
// </vc-helpers>

// <vc-spec>
fn ravel(a: Vec<f32>) -> (result: Vec<f32>)
    ensures result@ == a@
// </vc-spec>
// <vc-code>
{
    a
}
// </vc-code>

}
fn main() {}