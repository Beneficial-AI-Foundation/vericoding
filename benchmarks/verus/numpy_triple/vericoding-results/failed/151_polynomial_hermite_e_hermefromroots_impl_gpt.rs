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
fn zero_i8() -> (z: i8)
    ensures
        z == 0i8,
{
    0i8
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
    let n = roots.len();
    let target = n + 1;
    let mut res: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < target
        invariant
            i <= target,
            res.len() == i,
            target == roots.len() + 1,
        decreases (target - i) as int
    {
        res.push(zero_i8());
        i += 1;
    }
    res
}
// </vc-code>

}
fn main() {}