// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): fixed nat/int usage in exec code */
    let mut result = Vec::new();
    for i in 0..x.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == poly_eval_at_point(x[j] as int, r@.map_values(|v: i32| v as int))
    {
        let mut prod: i32 = 1;
        for j in 0..r.len()
            invariant
                0 <= i < x.len(),
                prod as int == poly_eval_at_point(x@[i as int] as int, r@.subrange(0, j as int).map_values(|v: i32| v as int))
        {
            let diff = (x[i] as i32).wrapping_sub(r[j] as i32);
            prod = prod.wrapping_mul(diff);
        }
        result.push(prod);
    }
    result
}
// </vc-code>

}
fn main() {}