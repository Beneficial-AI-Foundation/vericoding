// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed int usage in executable code, using usize/isize */
spec fn pi() -> f64 {
    3.141592653589793238462643383279502884197
}

fn compute_chebyshev_nodes(deg: usize) -> (nodes: Vec<f64>)
    ensures
        nodes.len() == deg + 1
{
    let mut nodes = Vec::new();
    let mut i: usize = 0;
    while i <= deg
        invariant
            nodes.len() == i,
            i <= deg + 1
    {
        let i_f64 = i as f64;
        let deg_f64 = deg as f64;
        let angle = pi() * (2.0 * i_f64 + 1.0) / (2.0 * (deg_f64 + 1.0));
        let node = angle.cos();
        nodes.push(node);
        i = i + 1;
    }
    nodes
}

fn evaluate_at_nodes(deg: usize, func: spec_fn(f64) -> f64) -> (values: Vec<f64>)
    ensures
        values.len() == deg + 1
{
    let nodes = compute_chebyshev_nodes(deg);
    let mut values = Vec::new();
    let mut i: usize = 0;
    while i <= deg
        invariant
            values.len() == i,
            i <= deg + 1,
            nodes.len() == deg + 1
    {
        let val = func(nodes[i]);
        values.push(val);
        i = i + 1;
    }
    values
}

fn compute_dct(values: Vec<f64>, deg: usize) -> (coef: Vec<f64>)
    requires
        values.len() == deg + 1
    ensures
        coef.len() == deg + 1
{
    let mut coef = Vec::new();
    let mut k: usize = 0;
    while k <= deg
        invariant
            coef.len() == k,
            k <= deg + 1,
            values.len() == deg + 1
    {
        let mut sum: f64 = 0.0;
        let mut j: usize = 0;
        while j <= deg
            invariant
                j <= deg + 1,
                values.len() == deg + 1
        {
            let k_f64 = k as f64;
            let j_f64 = j as f64;
            let deg_f64 = deg as f64;
            let angle = pi() * k_f64 * (2.0 * j_f64 + 1.0) / (2.0 * (deg_f64 + 1.0));
            sum = sum + values[j] * angle.cos();
            j = j + 1;
        }
        let deg_f64 = deg as f64;
        let scale = if k == 0 { 1.0 / (deg_f64 + 1.0) } else { 2.0 / (deg_f64 + 1.0) };
        coef.push(sum * scale);
        k = k + 1;
    }
    coef
}
// </vc-helpers>

// <vc-spec>
spec fn is_constant_function(func: spec_fn(f64) -> f64) -> bool {
    forall|x: f64, y: f64| #[trigger] func(x) == #[trigger] func(y)
}

fn chebinterpolate(deg: usize, func: spec_fn(f64) -> f64) -> (coef: Vec<f64>)
    ensures 
        coef.len() == deg + 1,
        /* The coefficients satisfy the key properties of Chebyshev interpolation:
           1. The coefficient vector has the correct length (guaranteed by type)
           2. When the function is constant, all coefficients except the first are zero */
        is_constant_function(func) ==> (
            coef[0] == func(0.0) &&
            forall|i: int| 1 <= i < coef.len() ==> #[trigger] coef[i] == 0.0
        )
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no change needed */
    let values = evaluate_at_nodes(deg, func);
    let coef = compute_dct(values, deg);
    coef
}
// </vc-code>


}
fn main() {}