// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed compilation error by changing the path of lemma_map_subrange to vstd::seq */
fn compute_poly_eval_at_point(x_val: i32, roots: &[i32]) -> (result: i32)
    ensures
        result as int == poly_eval_at_point(x_val as int, old(roots)@.map_values(|v: i32| v as int)),
    decreases roots.len(),
{
    if roots.len() == 0 {
        1
    } else {
        proof {
            let roots_seq = old(roots)@;
            let f = |v: i32| v as int;
            vstd::seq::lemma_map_subrange(roots_seq, 1, roots_seq.len() as int, f);
        }
        let sub_eval = compute_poly_eval_at_point(x_val, &roots[1..]);
        (x_val - roots[0]) * sub_eval
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
    /* code modified by LLM (iteration 5): logic is sound, no changes made */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result@[j] == poly_eval_at_point(x@[j] as int, r@.map_values(|v: i32| v as int)),
    {
        let y_val = compute_poly_eval_at_point(x[i], r.as_slice());
        result.push(y_val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}