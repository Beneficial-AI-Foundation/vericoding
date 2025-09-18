// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed syntax error by removing erroneous ensures clause */
spec fn all_within_tolerance(c: Vec<f32>, start: usize, tol: f32) -> bool
    recommends start <= c.len()
{
    forall|i: int| start <= i < c.len() ==> c[i as usize].abs() <= tol
}

fn find_last_significant(c: Vec<f32>, tol: f32) -> (result: usize)
    requires c.len() >= 1
    ensures result < c.len()
{
    let mut i = c.len() - 1;
    while i > 0 && c[i].abs() <= tol
        invariant i < c.len()
        decreases i
    {
        i = i - 1;
    }
    i
}
// </vc-helpers>

// <vc-spec>
fn trimcoef(c: Vec<f32>, tol: f32) -> (result: Vec<f32>)
    ensures
        result.len() >= 1,
        result.len() <= c.len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed syntax error by adding braces around invariants */
{
    if c.len() == 0 {
        return vec![0.0f32];
    }
    
    let last_idx = find_last_significant(c, tol);
    let mut result = Vec::new();
    
    for i in 0..=last_idx
        invariant {
            result.len() == i &&
            i <= last_idx + 1 &&
            last_idx < c.len()
        }
    {
        result.push(c[i]);
    }
    
    if result.len() == 0 {
        result.push(0.0f32);
    }
    
    result
}
// </vc-code>

}
fn main() {}