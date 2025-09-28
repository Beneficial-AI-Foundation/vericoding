// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed compilation error by correcting the ensures clause to use result instead of the undefnied local variable product */
fn eval_poly_at_x(x_val: i64, roots: &Vec<i8>) -> i64
    ensures
        result as int == poly_eval_at_point(x_val as int, roots@.map_values(|v: i8| v as int))
{
    let mut product: i64 = 1;
    for i in 0..roots.len() {
        product *= (x_val - roots[i] as i64);
    }
    product
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
/* code modified by LLM (iteration 2): fixed compilation errors and removed verification bypasses */
{
    let mut result = Vec::with_capacity(x.len());
    for j in 0..x.len() {
        let val = eval_poly_at_x(x[j] as i64, &r);
        result.push(val as i8);
    }
    result
}
// </vc-code>

}
fn main() {}