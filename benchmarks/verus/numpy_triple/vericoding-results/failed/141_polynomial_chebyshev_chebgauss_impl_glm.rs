// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): combined ensures conditions into one block */
fn chebyshev_nodes(n: u8) -> Vec<f32>
    requires n > 0,
    ensures
        result.len() == n as usize,
        forall|i: int, j: int| 0 <= i < n as int && 0 <= j < n as int && i != j ==> #[trigger] result[i] != #[trigger] result[j],
{
    let mut nodes = Vec::with_capacity(n as usize);
    let mut i = 0;
    while i < n
        invariant 0 <= i <= n,
        invariant nodes.len() == i as usize,
        invariant forall|k: int, l: int| 0 <= k < i && 0 <= l < i && k != l ==> #[trigger] nodes[k] != #[trigger] nodes[l],
        decreases n - i,
    {
        let angle = (2 * i + 1) as f32 * std::f32::consts::PI / (2 * n) as f32;
        let node = angle.cos();
        nodes.push(node);
        i += 1;
    }
    nodes
}

/* helper modified by LLM (iteration 5): combined ensures conditions into one block */
fn uniform_weights(n: u8) -> Vec<f32>
    requires n > 0,
    ensures
        result.len() == n as usize,
        forall|i: int, j: int| 0 <= i < n as int && 0 <= j < n as int ==> #[trigger] result[i] == #[trigger] result[j],
{
    let weight = 1.0 / (n as f32);
    let mut weights = Vec::with_capacity(n as usize);
    let mut i = 0;
    while i < n
        invariant 0 <= i <= n,
        invariant weights.len() == i as usize,
        invariant forall|k: int| 0 <= k < i ==> #[trigger] weights[k] == weight,
        decreases n - i,
    {
        weights.push(weight);
        i += 1;
    }
    weights
}
// </vc-helpers>

// <vc-spec>
fn chebgauss(n: u8) -> (result: (Vec<f32>, Vec<f32>))
    requires n > 0,
    ensures
        result.0.len() == n as usize,
        result.1.len() == n as usize,
        /* All weights are equal (uniform weights) */
        forall|i: int, j: int| 0 <= i < n as int && 0 <= j < n as int ==> 
            #[trigger] result.1[i] == #[trigger] result.1[j],
        /* Nodes are distinct */
        forall|i: int, j: int| 0 <= i < n as int && 0 <= j < n as int && i != j ==> 
            #[trigger] result.0[i] != #[trigger] result.0[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no changes needed */
    let nodes = chebyshev_nodes(n);
    let weights = uniform_weights(n);
    (nodes, weights)
}
// </vc-code>


}
fn main() {}