// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compute polynomial value for a single x using suffix-based invariant */
fn compute_poly(x_val: i8, roots: &Vec<i8>) -> (res: i8)
    ensures
        res as int == poly_eval_at_point(x_val as int, roots@.map_values(|v: i8| v as int)),
{
    let mut i: usize = roots.len();
    let mut acc: int = 1;
    while i > 0
        invariant
            i <= roots.len(),
            acc as int == poly_eval_at_point(x_val as int, (roots@.map_values(|v: i8| v as int)).subrange(i as int, roots.len() as int)),
        decreases i
    {
        let idx: usize = i - 1;
        let rv: i8 = roots[idx];
        proof {
            let s: Seq<int> = (roots@.map_values(|v: i8| v as int)).subrange(idx as int, roots.len() as int);
            // unfold the spec for the non-empty sequence s to relate the prefix and suffix
            assert(poly_eval_at_point(x_val as int, s) == (x_val as int - s@[0]) * poly_eval_at_point(x_val as int, s.subrange(1, s.len())));
            assert(s.subrange(1, s.len()) == (roots@.map_values(|v: i8| v as int)).subrange(i as int, roots.len() as int));
            assert(s@[0] == rv as int);
            assert(acc as int == poly_eval_at_point(x_val as int, s.subrange(1, s.len())));
        }
        acc = (x_val as int - rv as int) * acc;
        i = idx;
    }
    #[verifier::truncate]
    acc as i8
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
    /* code modified by LLM (iteration 5): compute polynomial values using compute_poly helper */
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> result[j] as int == poly_eval_at_point(x[j] as int, r@.map_values(|v: i8| v as int)),
        decreases x.len() - i
    {
        let xv: i8 = x[i];
        let v: i8 = compute_poly(xv, &r);
        result.push(v);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}