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
/* helper modified by LLM (iteration 5): removed int casts in exec code */
proof fn lemma_product_form_base(roots: Seq<int>, x: int)
    ensures product_form(roots, x, 0) == 1
{
}

proof fn lemma_product_form_step(roots: Seq<int>, x: int, i: nat)
    requires i > 0, i <= roots.len()
    ensures product_form(roots, x, i) == product_form(roots, x, (i - 1) as nat) * (x - roots[(i - 1) as int])
{
}

fn expand_polynomial(roots: Vec<i8>) -> (result: Vec<i8>)
    ensures result.len() == roots.len() + 1
{
    let mut coeffs = Vec::new();
    coeffs.push(1);
    
    let mut i = 0;
    while i < roots.len()
        invariant
            0 <= i <= roots.len(),
            coeffs.len() == i + 1,
        decreases roots.len() - i
    {
        let root = roots[i];
        let mut new_coeffs = Vec::new();
        new_coeffs.push(0);
        
        let mut j = 0;
        while j < coeffs.len()
            invariant
                0 <= j <= coeffs.len(),
                new_coeffs.len() == j + 1,
                coeffs.len() > 0,
            decreases coeffs.len() - j
        {
            if j == 0 {
                let val = (-root * coeffs[j]) as i8;
                new_coeffs.set(0, val);
            } else {
                let val1 = coeffs[j - 1];
                let val2 = root * coeffs[j];
                let result_val = (val1 - val2) as i8;
                new_coeffs.push(result_val);
            }
            j += 1;
        }
        new_coeffs.push(coeffs[coeffs.len() - 1]);
        coeffs = new_coeffs;
        i += 1;
    }
    
    coeffs
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
/* code modified by LLM (iteration 5): no changes needed */
{
    if roots.len() == 0 {
        let mut result = Vec::new();
        result.push(1);
        result
    } else {
        expand_polynomial(roots)
    }
}
// </vc-code>

}
fn main() {}