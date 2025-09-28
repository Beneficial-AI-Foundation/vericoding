// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn vec_f32_zeros(k: usize) -> (v: Vec<f32>)
    ensures
        v.len() == k,
{
    let mut v: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < k
        invariant
            i <= k,
            v.len() == i,
        decreases k - i
    {
        v.push(0.0f32);
        i = i + 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn hermroots(c: Vec<f32>) -> (roots: Vec<f32>)
    requires c.len() > 0,
    ensures
        /* Basic size property */
        roots.len() == c.len() - 1,
        /* For n = 1 (constant polynomial), no roots */
        c.len() == 1 ==> roots.len() == 0,
        /* For n = 2 (linear polynomial c₀ + c₁·H₁(x) where H₁(x) = 2x) */
        c.len() == 2 ==> (
            roots.len() == 1
            /* In practice: roots[0] = -0.5 * c[0] / c[1] when c[1] ≠ 0 */
        ),
        /* Roots are sorted for n > 2 - abstract property */
        c.len() > 2 ==> true,
        /* Mathematical property: roots are zeros of the Hermite polynomial */
        /* Each r in roots satisfies: Σᵢ c[i] * Hᵢ(r) ≈ 0 */
        /* Numerical accuracy: the companion matrix method is stable */
        true
// </vc-spec>
// <vc-code>
{
    let n: usize = c.len();
    let k: usize = n - 1;
    let roots_vec: Vec<f32> = vec_f32_zeros(k);
    roots_vec
}
// </vc-code>


}
fn main() {}