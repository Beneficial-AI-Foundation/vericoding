// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn lstsq(a: Vec<Vec<f32>>, b: Vec<f32>) -> (result: Vec<f32>)
    requires 
        a.len() > 0,
        b.len() > 0,
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i].len() > 0,
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i].len() == a[0].len(),
    ensures
        result.len() == a[0].len()
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