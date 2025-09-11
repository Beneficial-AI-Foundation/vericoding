// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn flipud(m: Vec<f32>) -> (result: Vec<f32>)
    ensures 
        result.len() == m.len(),
        forall|i: int| 0 <= i < m.len() ==> result[i] == m[m.len() - 1 - i],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}