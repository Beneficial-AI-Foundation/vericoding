// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed syntax errors and improved herm_coeff calculation */
spec fn herm_coeff(pol: Vec<f64>, i: int) -> f64 
    recommends 
        0 <= i < pol.len()
{
    if pol.len() == 0 {
        0.0
    } else if i == 0 {
        pol[0]
    } else {
        let prev = herm_coeff(pol, i - 1);
        let sign = if i % 2 == 0 { 1.0f64 } else { -1.0f64 };
        let term_val = pol[i].spec_euclidean_div(factorial(i) as f64);
        prev.spec_add(sign.spec_mul(term_val))
    }
}

spec fn factorial(n: int) -> int 
    decreases n
{
    if n <= 0 {
        1
    } else {
        n * factorial(n - 1)
    }
}

proof fn poly_zero_implies_herm_zero(pol: Vec<f64>) 
    requires 
        pol.len() >= 0,
        forall|i: int| 0 <= i < pol.len() ==> pol[i] == 0.0
    ensures 
        forall|i: int| 0 <= i < pol.len() ==> (#[trigger] herm_coeff(pol, i)) == 0.0
{
    if pol.len() > 0 {
        let subvec = pol.subrange(0, pol.len() - 1);
        poly_zero_implies_herm_zero(subvec);
    }
}
// </vc-helpers>

// <vc-spec>
fn poly2herm(pol: Vec<f64>) -> (result: Vec<f64>)
    ensures
        result.len() == pol.len(),

        (forall|i: int| 0 <= i < pol.len() ==> pol[i] == 0.0) ==> 
            (forall|i: int| 0 <= i < result.len() ==> result[i] == 0.0),

        pol.len() > 0 ==> 
            (forall|i: int| 1 <= i < pol.len() ==> pol[i] == 0.0) ==>
                result[0] == pol[0],

        (pol.len() == 4 && pol[0] == 0.0 && pol[1] == 1.0 && 
         pol[2] == 2.0 && pol[3] == 3.0) ==>
            (result[0] == 1.0 && result[1] == 2.75 && 
             result[2] == 0.5 && result[3] == 0.375)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation errors and improved implementation */
{
    let n = pol.len();
    let mut result = Vec::new();
    
    if n == 0 {
        return result;
    }
    
    result.push(pol[0]);
    
    let mut i_ghost: int = 1;
    for i in 1..n {
        proof {
            i_ghost = i as int;
        }
        let sign = if i % 2 == 0 { 1.0f64 } else { -1.0f64 };
        let fact_i = factorial(i_ghost) as f64;
        let term = sign.spec_mul(pol[i].spec_euclidean_div(fact_i));
        let prev = *result.last().unwrap();
        result.push(prev.spec_add(term));
    }
    
    result
}
// </vc-code>

}
fn main() {}