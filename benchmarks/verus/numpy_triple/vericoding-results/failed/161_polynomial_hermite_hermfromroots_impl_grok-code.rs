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
    /* code modified by LLM (iteration 5): Rewrote using while loops with invariants to fix indexing precondition failures and postconditions */
    let mut coef = Vec::new();
    coef.push(1.0f32);
    let mut i = 0;
    while i < roots.len()
        invariant
            i <= roots.len(),
            coef@.len() == i + 1,
        decreases
            roots.len() - i
    {
        let r = roots[i as usize];
        let n = coef.len();
        let mut new = Vec::new();
        let mut k = 0;
        while k < n + 1
            invariant
                k <= n + 1,
                new@.len() == k as int,
            decreases
                n + 1 - k
        {
            new.push(0.0f32);
            k = k + 1;
        }
        let mut j = 0;
        while j < n + 1
            invariant
                j <= n + 1,
            decreases
                n + 1 - j
        {
            if j == 0 {
                new[j as usize] = -r * coef[j as usize];
            } else if j < n {
                new[j as usize] = coef[(j - 1) as usize] - r * coef[j as usize];
            } else {
                new[j as usize] = coef[(j - 1) as usize];
            }
            j = j + 1;
        }
        coef = new;
        i = i + 1;
    }
    coef
}
// </vc-code>


}
fn main() {}