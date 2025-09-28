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
/* helper modified by LLM (iteration 5): added requires clause for `len` to make it non-negative. */
pub fn make_vec_with_length(len: usize) -> (v: Vec<i8>)
    requires len >= 0
    ensures v.len() == len
{
    let mut v: Vec<i8> = Vec::new();
    let mut i = 0;
    while i < len
        invariant
            0 <= i && i <= len,
            v.len() == i,
        decreases len - i
    {
        v.push(0);
        i = i + 1;
    }
    v
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
/* code modified by LLM (iteration 5): Corrected type casting and underflow/overflow issues. Ensured all calculations are done with `i32` to avoid truncation before the final assignment. 
Added condition for `coeffs_len` being positive before accessing `product_coeffs[coeffs_len - 1]`. Improved loop invariants for `next_product_coeffs` to correctly reflect its state. 
Also added invariant `product_coeffs.len() == k + 1` to the outer loop to ensure proper indexing. */
{
    let n = roots.len();
    if n == 0 {
        let mut coeffs: Vec<i8> = Vec::new();
        coeffs.push(1);
        return coeffs;
    }

    let mut product_coeffs: Vec<i8> = Vec::new();
    product_coeffs.push(1);

    let mut coeffs_len = 1;

    let mut k = 0;
    while k < n
        invariant
            0 <= k && k <= n,
            coeffs_len == k + 1,
            product_coeffs.len() == k + 1,
            product_coeffs.len() == coeffs_len,
        decreases n - k
    {
        let root_val: i32 = roots[k] as i32;
        let mut next_product_coeffs: Vec<i8> = make_vec_with_length(coeffs_len + 1);

        next_product_coeffs[0] = (-root_val * (product_coeffs[0] as i32)) as i8;

        let mut i = 1;
        while i < coeffs_len
            invariant
                1 <= i && i <= coeffs_len,
                product_coeffs.len() == coeffs_len,
                next_product_coeffs.len() == coeffs_len + 1,
            decreases coeffs_len - i
        {
            let term1 = product_coeffs[i - 1] as i32;
            let term2 = root_val * (product_coeffs[i] as i32);
            next_product_coeffs[i] = (term1 - term2) as i8;
            i = i + 1;
        }
        if coeffs_len > 0 {
            next_product_coeffs[coeffs_len] = product_coeffs[coeffs_len - 1];
        }

        product_coeffs = next_product_coeffs;
        coeffs_len = coeffs_len + 1;
        k = k + 1;
    }

    product_coeffs
}
// </vc-code>

}
fn main() {}