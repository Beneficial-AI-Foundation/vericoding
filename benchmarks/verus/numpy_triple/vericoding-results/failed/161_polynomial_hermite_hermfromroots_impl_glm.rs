// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed f32 arithmetic operations by using standard operators */
fn hermfromroots_helper(roots: Vec<f32>, i: usize, j: usize) -> (f32)
    requires
        i < roots.len(),
        j < roots.len(),
        i != j,
    ensures
        hermfromroots_helper(roots, i, j) == 1.0f32 / (roots@[i as int] - roots@[j as int])
{
    1.0f32 / (roots[i] - roots[j])
}

/* helper modified by LLM (iteration 4): changed parameter from int to usize and adjusted invariants */
fn hermfromroots_poly(roots: Vec<f32>, k: usize) -> (Vec<f32>)
    requires
        k < roots.len(),
    ensures
        hermfromroots_poly(roots, k)@.len() == roots@.len(),
        forall|i: int| 0 <= i < roots@.len() ==> hermfromroots_poly(roots, k)@[i] != 0.0f32
{
    let mut poly = Vec::new();
    let ghost n_ghost = roots@.len() as int;
    let n = roots.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            poly@.len() == (i as int),
            forall|j: int| 0 <= j < (i as int) ==> poly@[j] != 0.0f32,
        decreases (n - i) as int
    {
        if i != k {
            poly.push(hermfromroots_helper(roots, k, i));
        } else {
            poly.push(1.0f32);
        }
        i += 1;
    }
    poly
}
// </vc-helpers>

// <vc-spec>
fn hermfromroots(roots: Vec<f32>) -> (coef: Vec<f32>)
    ensures
        coef@.len() == roots@.len() + 1,
        roots@.len() > 0 ==> coef@[roots@.len() as int] != 0.0f32
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed f32 arithmetic operations by using standard operators */
{
    let ghost n_ghost = roots@.len() as int;
    let n = roots.len();
    let mut coef = Vec::new();
    let mut i: usize = 0;
    while i <= n
        invariant
            0 <= (i as int) <= n_ghost + 1,
            coef@.len() == i as int,
            i > 0 ==> coef@[(i-1) as int] != 0.0f32,
        decreases (n_ghost + 1) - (i as int)
    {
        if i == 0 {
            coef.push(1.0f32);
        } else {
            let mut sum = 0.0f32;
            let mut j: usize = 0;
            while j < n
                invariant
                    0 <= (j as int) <= n_ghost,
                    j > 0 ==> sum != 0.0f32,
                decreases n_ghost - (j as int)
            {
                let poly = hermfromroots_poly(roots, j);
                sum += poly[(i - 1) as usize];
                j += 1;
            }
            coef.push(sum);
        }
        i += 1;
    }
    coef
}
// </vc-code>


}
fn main() {}