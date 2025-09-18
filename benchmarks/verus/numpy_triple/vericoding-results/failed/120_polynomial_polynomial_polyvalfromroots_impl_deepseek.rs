// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed ghost function syntax and added proper helper functions */
proof fn poly_eval_lemma(x_val: int, roots: Seq<int>)
    requires roots.len() >= 0
    ensures poly_eval_at_point(x_val, roots) == poly_eval_at_point(x_val, roots)
    decreases roots.len()
{
    if roots.len() > 0 {
        poly_eval_lemma(x_val, roots.subrange(1, roots.len() as int));
    }
}

spec fn seq_to_int_seq(s: Seq<i32>) -> Seq<int> {
    s.map_values(|val: i32| val as int)
}

proof fn get_x_val_ghost(x: Vec<i32>, i: int) -> int
    requires 0 <= i < x.len()
{
    x@[i] as int
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
/* code modified by LLM (iteration 5): Fixed compilation error by using ghost variable for x[i] as int */
{
    let mut result = Vec::new();
    let root_seq = seq_to_int_seq(r@);
    
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == poly_eval_at_point(x[j] as int, root_seq)
    {
        ghost {
            let x_val_ghost = get_x_val_ghost(x, i as int);
        }
        let eval_result = poly_eval_at_point(x[i] as int, root_seq);
        result.push(eval_result as i32);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}