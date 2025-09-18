// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type conversions and nat usage */
spec fn hermite_step(prev: f32, curr: f32, x: f32) -> f32 {
    curr * x + prev
}

spec fn hermite_eval_inner(seq: Seq<f32>, x: f32, start_index: int) -> f32 
    decreases seq.len() as int - start_index when start_index >= 0 && start_index <= seq.len() as int
{
    if start_index >= seq.len() as int {
        0.0
    } else if start_index == seq.len() as int - 1 {
        seq[start_index as nat]
    } else {
        hermite_step(
            hermite_eval_inner(seq, x, start_index + 1),
            seq[start_index as nat],
            x
        )
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
/* code modified by LLM (iteration 5): fixed nat type conversion */
{
    let len = coef.len() as nat;
    let mut result = coef[(len - 1) as usize];
    let mut i: nat = len - 1;
    
    while i > 0
        invariant
            i >= 0 && i < len,
            result == hermite_eval_inner(coef@, x, i as int)
        decreases i
    {
        i = i - 1;
        result = hermite_step(result, coef[i as usize], x);
    }
    
    result
}
// </vc-code>

}
fn main() {}