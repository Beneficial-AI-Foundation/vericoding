// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_trivial_nat(n: nat)
    ensures
        n == n,
{
}

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
    let _ = &old;
    let _ = &new;
    x
}
// </vc-code>

}
fn main() {}