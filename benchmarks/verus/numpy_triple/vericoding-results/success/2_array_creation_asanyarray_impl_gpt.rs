// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn helper_lemma_trivial(x: int) ensures x == x { }
// </vc-helpers>

// <vc-spec>
fn asanyarray(a: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i],
// </vc-spec>
// <vc-code>
{
    a
}
// </vc-code>

}
fn main() {}