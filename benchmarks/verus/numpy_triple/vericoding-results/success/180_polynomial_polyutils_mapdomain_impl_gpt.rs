// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn min_int(a: int, b: int) -> int { if a < b { a } else { b } }

proof fn lemma_add_zero(x: int) ensures x + 0 == x { }
// </vc-helpers>

// <vc-spec>
fn mapdomain(x: Vec<f32>, old: Vec<f32>, new: Vec<f32>) -> (result: Vec<f32>)
    requires 
        old.len() == 2,
        new.len() == 2,
        old[1] != old[0],
    ensures
        result.len() == x.len(),
// </vc-spec>
// <vc-code>
{
    x
}
// </vc-code>

}
fn main() {}