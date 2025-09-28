// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hermfromroots(roots: Vec<f32>) -> (coef: Vec<f32>)
    ensures
        coef@.len() == roots@.len() + 1,
        roots@.len() > 0 ==> coef@[roots@.len() as int] != 0.0f32
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed array access bounds in invariants */
    let n = roots.len();
    let mut coef: Vec<f32> = Vec::new();
    coef.push(1.0f32);
    
    let mut i: usize = 0;
    while i < n
        invariant
            coef@.len() == i + 1,
            i <= n,
            i > 0 ==> coef@[i as int] != 0.0f32,
        decreases n - i
    {
        let root = roots[i];
        let mut new_coef: Vec<f32> = Vec::new();
        new_coef.push(0.0f32 - root * coef[0]);
        
        let mut j: usize = 1;
        while j <= i
            invariant
                new_coef@.len() == j,
                j >= 1,
                j <= i + 1,
                coef@.len() == i + 1,
                j <= coef@.len(),
            decreases i + 1 - j
        {
            let term = coef[j] - root * coef[j - 1];
            new_coef.push(term);
            j = j + 1;
        }
        
        new_coef.push(coef[i]);
        coef = new_coef;
        i = i + 1;
    }
    
    coef
}
// </vc-code>


}
fn main() {}