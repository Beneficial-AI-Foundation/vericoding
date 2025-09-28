// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): changed parameter types to usize to allow safe f32 casting */
fn compute_weight(n: usize) -> (result: f32)
    requires n > 0,
    ensures true
{
    std::f32::consts::PI / (n as f32)
}

/* helper modified by LLM (iteration 5): changed parameter types to usize to allow safe f32 casting */
fn compute_node(i: usize, n: usize) -> (result: f32)
    requires 0 <= i && i < n,
    ensures true
{
    let arg = ((2 * i + 1) as f32 * std::f32::consts::PI) / (2.0 * (n as f32));
    arg.cos()
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
/* code modified by LLM (iteration 5): adjusted function calls to use usize parameters for casting */
{
    let mut nodes = Vec::<f32>::new();
    let mut weights = Vec::<f32>::new();
    let weight = compute_weight(n as usize);
    for i in 0..(n as usize) {
        let node = compute_node(i, n as usize);
        nodes.push(node);
        weights.push(weight);
    }
    (nodes, weights)
}
// </vc-code>


}
fn main() {}