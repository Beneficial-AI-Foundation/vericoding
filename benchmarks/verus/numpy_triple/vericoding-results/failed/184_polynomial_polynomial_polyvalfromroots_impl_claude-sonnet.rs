// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed lemma declaration syntax by adding fn keyword */
fn lemma poly_eval_step(x_val: int, roots: Seq<int>, j: nat)
    requires j < roots.len()
    ensures poly_eval_at_point(x_val, roots.subrange(0, j as int + 1)) == 
        (x_val - roots[j as int]) * poly_eval_at_point(x_val, roots.subrange(0, j as int))
{
    if j == 0 {
        assert(roots.subrange(0, 0).len() == 0);
        assert(poly_eval_at_point(x_val, roots.subrange(0, 0)) == 1);
    } else {
        assert(roots.subrange(0, j as int + 1) == roots.subrange(0, j as int).push(roots[j as int]));
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
{
    /* code modified by LLM (iteration 5): fixed polynomial evaluation logic with proper wrapping multiplication */
    let mut result = Vec::new();
    for i in 0..x.len()
        invariant
            result.len() == i,
            i <= x.len(),
            forall|j: int| 0 <= j < i ==> result[j] as int == poly_eval_at_point(x[j] as int, r@.map_values(|v: i8| v as int)),
    {
        let mut poly_val = 1i8;
        for j in 0..r.len()
            invariant
                j <= r.len(),
                i < x.len(),
                poly_val as int == poly_eval_at_point(x[i] as int, r@.subrange(0, j as int).map_values(|v: i8| v as int)),
        {
            let diff = x[i].wrapping_sub(r[j]);
            poly_val = poly_val.wrapping_mul(diff);
        }
        result.push(poly_val);
    }
    result
}
// </vc-code>

}
fn main() {}