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

/* helper modified by LLM (iteration 5): Fixed ghost code usage and proper nat/int handling */
spec fn poly_from_roots(roots: Seq<int>, i: nat) -> Seq<int> 
    decreases i
{
    if i == 0 {
        Seq::new(1, |j: int| if j == 0 { 1 } else { 0 })
    } else {
        let prev = poly_from_roots(roots, (i - 1) as nat);
        let current_root = roots[(i - 1) as nat];
        let mut new_poly = Seq::new(prev.len() + 1, |j: int| 
            if j == 0 { -current_root * prev@[0] } 
            else if j < prev.len() { prev@[j - 1] - current_root * prev@[j] }
            else { prev@[j - 1] }
        );
        new_poly
    }
}

proof fn hermite_e_poly_coeffs_agreement(root_poly: Seq<int>, roots: Seq<int>) 
    ensures 
        forall|x: int| eval_hermite_e_poly(root_poly, x) == product_form(roots, x, roots.len()),
    decreases roots.len()
{
    if roots.len() > 0 {
        let smaller_roots = roots.subrange(0, roots.len() as int - 1);
        let smaller_poly = poly_from_roots(smaller_roots, smaller_roots.len());
        hermite_e_poly_coeffs_agreement(smaller_poly, smaller_roots);
        
        // Expand the inductive proof
        assert forall|x: int| eval_hermite_e_poly(root_poly, x) == product_form(roots, x, roots.len()) by {
            let last_root = roots[roots.len() as int - 1];
            assert(eval_hermite_e_poly(root_poly, x) == eval_hermite_e_poly(smaller_poly, x) * (x - last_root));
            assert(product_form(roots, x, roots.len()) == product_form(smaller_roots, x, smaller_roots.len()) * (x - last_root));
        };
    }
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
    /* code modified by LLM (iteration 5): Fixed int/nat compilation errors and ghost code usage */
    ghost {
        let n = roots.len();
        let mut coeffs = Vec::new();
        coeffs.push(1);
        
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                coeffs.len() == i + 1,
        {
            let current_root = roots[i] as int;
            let mut new_coeffs = Vec::new();
            new_coeffs.push(-current_root * coeffs[0]);
            
            let len_coeffs = coeffs.len();
            let mut j: usize = 0;
            while j < len_coeffs - 1
                invariant
                    0 <= j <= len_coeffs - 1,
                    new_coeffs.len() == j + 1,
            {
                new_coeffs.push(coeffs[j] - current_root * coeffs[j + 1]);
                j += 1;
            }
            
            new_coeffs.push(coeffs[len_coeffs - 1]);
            coeffs = new_coeffs;
            i += 1;
        }
        
        let mut result = Vec::new();
        let mut k: usize = 0;
        while k < coeffs.len()
            invariant
                0 <= k <= coeffs.len(),
                result.len() == k,
        {
            result.push(coeffs[k] as i8);
            k += 1;
        }
        
        result
    }
}
// </vc-code>

}
fn main() {}