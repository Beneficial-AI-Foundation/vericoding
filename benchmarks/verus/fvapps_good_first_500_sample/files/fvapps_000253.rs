// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn max_probability(n: usize, edges: Vec<Vec<usize>>, probs: Vec<f64>, s: usize, t: usize) -> (result: f64)
    requires 
        n >= 2,
        s < n,
        t < n,
        edges.len() == probs.len(),
        forall|i: int| 0 <= i < edges.len() ==> edges[i].len() == 2,
        forall|i: int| 0 <= i < edges.len() ==> edges[i][0] < n && edges[i][1] < n,
        forall|i: int| 0 <= i < edges.len() ==> edges[i][0] != edges[i][1],
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0.0
    // impl-end
}
// </vc-code>


}
fn main() {}