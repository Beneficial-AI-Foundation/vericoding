// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fixed compilation syntax for ensures clause and function body */
fn poly_eval_exec(x_val: i32, roots: &Vec<i32>, start: usize) -> (res: i32)
    requires start <= roots.len()
    decreases roots.len() - start
    ensures res as int == poly_eval_at_point(x_val as int, roots@[start as int..].map_values(|v: i32| v as int))
{
    if start == roots.len() {
        1
    } else {
        let sub_res = poly_eval_exec(x_val, roots, start + 1);
        let diff = x_val - roots[start];
        let val = diff * sub_res;
        val
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

fn polyvalfromroots(x: Vec<i32>, r: Vec<i32>) -> (result: Vec<i32>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == poly_eval_at_point(x[i] as int, r@.map_values(|v: i32| v as int)),
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 2): Implemented loop to compute polynomial values at each x point using helper */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] as int == poly_eval_at_point(x[j] as int, r@.map_values(|v: i32| v as int))
    {
        let val = poly_eval_exec(x[i], &r, 0);
        result.push(val);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}