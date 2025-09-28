// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed specification to avoid compilation error */
fn compute_poly_eval(x_val: int, roots: Seq<int>) -> int {
    if roots.len() == 0 {
        1
    } else {
        (x_val - roots[0]) * compute_poly_eval(x_val, roots.subrange(1, roots.len() as int))
    }
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

fn polyvalfromroots(x: Vec<i8>, r: Vec<i8>) -> (result: Vec<i8>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == poly_eval_at_point(x[i] as int, r@.map_values(|v: i8| v as int)),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): removed specification from helper function to avoid compilation error */
{
    let roots_seq = r@.map_values(|v: i8| v as int);
    let mut result = Vec::with_capacity(x.len());
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] as int == poly_eval_at_point(x[j] as int, roots_seq),
        decreases x.len() - i
    {
        let eval = compute_poly_eval(x[i] as int, roots_seq);
        result.push(eval as i8);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}