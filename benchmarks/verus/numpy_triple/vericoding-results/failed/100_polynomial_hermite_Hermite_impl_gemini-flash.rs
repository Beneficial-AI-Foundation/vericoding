// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected type mismatches by ensuring index access with `nat` and `i - 1` with `nat` type. This involves using `(i - 1) as nat` for recursive calls to satisfy type constraints. */
fn hermite_eval_spec(coef_seq: Seq<f32>, x: f32, i: nat) -> f32
    recommends i < coef_seq.len()
    decreases i
{
    if i == (0 as nat) {
        coef_seq.index(0 as nat)
    } else {
        coef_seq.index(i) + x * hermite_eval_spec(coef_seq, x, (i.checked_sub(1)).unwrap())
    }
}
// </vc-helpers>

// <vc-spec>
fn hermite_eval(coef: Vec<f32>, x: f32) -> (result: f32)
    requires coef.len() > 0,
    ensures 
        coef.len() == 1 ==> result == coef[0],
        coef.len() >= 2 ==> true,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Applied the `hermite_eval_spec` for calculation in loop invariant to align with the specification. The `result` definition now uses the recursive specification directly. */
{
    if coef.len() == 1 {
        return coef[0];
    }

    let mut i: usize = coef.len() - 1;
    let mut result: f32 = coef[i];

    while (i > 0)
        invariant
            0 < coef.len(),
            i < coef.len(),
            result == hermite_eval_spec(coef@, x, i as nat)
        decreases i
    {
        i = i - 1;
        result = coef[i] + x * result;
    }
    result
}
// </vc-code>

}
fn main() {}