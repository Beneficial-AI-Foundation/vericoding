// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn hermevander(x: Vec<f64>, deg: u8) -> (result: Vec<Vec<f64>>)
    requires deg as nat >= 0,
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == deg as nat + 1,
        forall|i: int| 0 <= i < result@.len() ==> result@[i][0] == 1.0,
        deg > 0 ==> forall|i: int| 0 <= i < result@.len() ==> result@[i][1] == x@[i],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}