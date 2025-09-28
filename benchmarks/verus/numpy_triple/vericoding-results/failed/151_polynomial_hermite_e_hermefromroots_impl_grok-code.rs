// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn eval_hermite_e(k: nat, x: int) -> int 
    decreases k
{
    if k == 0 {
        1
    } else if k == 1 {
        x
    } else {
        x * eval_hermite_e((k - 1) as nat, x) - (k - 1) as int * eval_hermite_e((k - 2) as nat, x)
    }
}

spec fn eval_hermite_e_poly(coeffs: Seq<int>, x: int) -> int 
    decreases coeffs.len()
{
    if coeffs.len() == 0 {
        0
    } else {
        coeffs[0] * eval_hermite_e(0, x) + eval_hermite_e_poly(coeffs.skip(1), x)
    }
}

spec fn product_form(roots: Seq<int>, x: int, i: nat) -> int 
    decreases i
{
    if i == 0 {
        1
    } else {
        product_form(roots, x, (i - 1) as nat) * (x - roots[(i - 1) as int])
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed syntax errors in parameter types and preconditions */
fn polynomial_multiply(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires
        a.len() >= 1,
        b.len() >= 1,
    ensures
        result.len() == a.len() + b.len() - 1,
{
    let mut res = Vec::with_capacity((a.len() + b.len() - 1) as usize);
    for _ in 0..(a.len() + b.len() - 1) {
        res.push(0i32);
    }
    for i in 0..a.len() {
        for j in 0..b.len() {
            let idx = i + j;
            let old_val = res[idx];
            res.set(idx, old_val + (*a)[i] * (*b)[j]);
        }
    }
    res
}
// </vc-helpers>

// <vc-spec>
fn hermefromroots(roots: Vec<i8>) -> (coeffs: Vec<i8>)
    ensures
        coeffs.len() == roots.len() + 1,

        (roots.len() == 0 ==> coeffs.len() == 1),

        (roots.len() > 0 ==> coeffs.len() == roots.len() + 1),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implemented the polynomial multiplication and root embedding logic */
    if roots.len() == 0 {
        vec![1i8]
    } else {
        let mut coeffs: Vec<i32> = vec![1i32];
        for i in 0..roots.len() {
            let r: i32 = roots[i] as i32;
            let mono: Vec<i32> = vec![1i32, -r];
            coeffs = polynomial_multiply(&coeffs, &mono);
        }
        let mut result: Vec<i8> = Vec::new();
        for i in 0..coeffs.len() {
            result.push(#[verifier::truncate] coeffs[i] as i8);
        }
        result
    }
}
// </vc-code>

}
fn main() {}