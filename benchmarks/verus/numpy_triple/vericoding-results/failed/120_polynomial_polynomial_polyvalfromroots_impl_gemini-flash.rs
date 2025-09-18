// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed helper */
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
/* code modified by LLM (iteration 5): fixed compilation errors by removing conversion to `int` in non-ghost code */
{
    let roots_spec = r@.map_values(|v: i32| v as int);
    let mut result = Vec::new();
    let mut i: usize = 0;

    while i < x.len()
        invariant
            0 <= i as int,
            i as int <= x.len() as int,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result[j] == poly_eval_at_point(x[j] as int, roots_spec),
    {
        let val_x_i32: i32 = x@[i];
        let mut current_product_i32: i32 = 1;
        let mut k: usize = 0;

        while k < r.len()
            invariant
                0 <= k as int,
                k as int <= r.len() as int,
                poly_eval_at_point(val_x_i32 as int, roots_spec.subrange(0, k as int))
                    == current_product_i32 as int,
        {
            let root_val_i32: i32 = r@[k];
            current_product_i32 = current_product_i32 * (val_x_i32 - root_val_i32);
            k = k + 1;
        }
        result.push(current_product_i32);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}