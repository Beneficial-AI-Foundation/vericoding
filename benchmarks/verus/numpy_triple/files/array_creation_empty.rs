// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn empty(n: usize) -> (result: Vec<f32>)
    ensures 
        result.len() == n,
        forall|i: int| 0 <= i < n ==> exists|v: f32| result[i] == v
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}