// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compute product in 128-bit to reduce overflow risk and use explicit loop invariants */
fn prod_i128(x: i32, roots: Vec<i32>) -> i128 {
    let mut p: i128 = 1;
    let mut i: usize = 0;
    while i < roots.len() {
        invariant(i <= roots.len());
        decreases(roots.len() - i);
        p = p * ((x as i128) - (roots[i] as i128));
        i += 1;
    }
    p
}
// </vc-helpers>

// <vc-spec>
spec fn poly_eval_at_point(x_val: int, roots: Seq<int>) -> int
    decreases roots.len()
{
    if roots.len() == 0 {
        1
    } else {
        (x_val - roots[0]) * poly_eval_at_point(x_val, roots.subrange(1, roots.len() as int))
    }
}

fn polyvalfromroots(x: Vec<i32>, r: Vec<i32>) -> (result: Vec<i32>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == poly_eval_at_point(x[i] as int, r@.map_values(|v: i32| v as int)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate over x, compute product via helper and cast with verifier truncate attribute */
    let mut result: Vec<i32> = Vec::new();
    result.reserve(x.len());
    let mut xi: usize = 0;
    while xi < x.len() {
        invariant(xi <= x.len());
        invariant(result.len() == xi);
        decreases(x.len() - xi);
        let prod = prod_i128(x[xi], r.clone());
        result.push(#[verifier::truncate] prod as i32);
        xi += 1;
    }
    result
}
// </vc-code>

}
fn main() {}