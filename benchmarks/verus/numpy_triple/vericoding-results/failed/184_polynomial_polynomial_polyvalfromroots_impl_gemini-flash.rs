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

fn polyvalfromroots(x: Vec<i8>, r: Vec<i8>) -> (result: Vec<i8>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == poly_eval_at_point(x[i] as int, r@.map_values(|v: i8| v as int)),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix compilation errors by using `usize` for indexing and loop bounds, and converting `int` to `usize` where necessary. */
{
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;

    while i < x.len()
        invariant
            0 <= i as int && i as int <= x.len() as int,
            result.len() == i,
            x.len() == old(x.len()),
            r.len() == old(r.len()),
            forall|j: int| 0 <= j < i as int ==> result[j as usize] as int == poly_eval_at_point(x[j as usize] as int, r@.map_values(|v: i8| v as int))
    {
        let mut current_val: i8 = 1;
        let mut k: usize = 0;
        while k < r.len()
            invariant
                0 <= k as int && k as int <= r.len() as int,
                x.len() == old(x.len()),
                r.len() == old(r.len()),
                i == old(i),
                result.len() == i,
        {
            // Perform calculation in i16 to prevent overflow before casting back to i8
            let operand_x = x[i] as i16;
            let operand_r = r[k] as i16;
            let term = operand_x - operand_r;
            current_val = ((current_val as i16) * term) as i8;
            k = k + 1;
        }
        result.push(current_val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}