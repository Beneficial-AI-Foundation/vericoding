// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed problematic u32 cast and used built-in f32 operations */
fn chebyshev_node(k: u8, n: u8) -> f32
    requires
        n > 0,
        k < n,
{
    let pi = 3.14159265359f32;
    let k_f32 = k as f32;
    let n_f32 = n as f32;
    let numerator = (2.0 * k_f32 + 1.0) * pi;
    let denominator = 2.0 * n_f32;
    (numerator / denominator).cos()
}

/* Helper function to compute uniform weight */
fn uniform_weight(n: u8) -> f32
    requires n > 0,
{
    let n_f32 = n as f32;
    3.14159265359f32 / n_f32
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
    /* code modified by LLM (iteration 5): removed problematic u32 cast and used direct u8 to f32 conversion */
    let mut nodes: Vec<f32> = Vec::new();
    let mut weights: Vec<f32> = Vec::new();
    
    let uniform_wt = uniform_weight(n);
    
    let mut k: u8 = 0;
    while k < n
        invariant
            k <= n,
            nodes.len() == k as usize,
            weights.len() == k as usize,
            forall|i: int, j: int| 0 <= i < k as int && 0 <= j < k as int ==> 
                #[trigger] weights[i] == #[trigger] weights[j],
            forall|i: int, j: int| 0 <= i < k as int && 0 <= j < k as int && i != j ==> 
                #[trigger] nodes[i] != #[trigger] nodes[j],
    {
        let node = chebyshev_node(k, n);
        nodes.push(node);
        weights.push(uniform_wt);
        k = k + 1;
    }
    
    (nodes, weights)
}
// </vc-code>


}
fn main() {}