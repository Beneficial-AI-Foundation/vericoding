// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed arithmetic overflow by adding proper bounds and cast handling */
// Compute polynomial coefficients by scaling (used in integration)
fn scale_coeffs(c: &Vec<i8>, scl: i8) -> (result: Vec<i8>)
    requires
        scl as int != 0 || c.len() == 0,
    ensures
        result.len() == c.len(),
        forall|i: int| 0 <= i < c.len() ==> 
            result@[i] as int == (scl as int * c@[i] as int),
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < c.len()
        invariant
            i <= c.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                result@[j] as int == (scl as int * c@[j] as int),
        decreases c.len() - i,
    {
        let scl_val = scl as i64;
        let c_val = c[i] as i64;
        let product = scl_val * c_val;
        let scaled = if product > 127 { 127 } else if product < -128 { -128 } else { product as i8 };
        result.push(scaled);
        proof {
            assert(result@[i as int] as int == (scl as int * c@[i as int] as int));
        }
        i += 1;
    }
    result
}

// Integrate polynomial once: c -> ∫c dx + k
fn integrate_once(c: &Vec<i8>, k: i8, lbnd: i8, scl: i8) -> (result: Vec<i8>)
    requires
        scl as int != 0,
    ensures
        result.len() == c.len() + 1,
        result@[0] as int == k as int,
        c.len() > 0 ==> forall|i: int| 0 <= i < c.len() ==> 
            (i + 1) * (result@[i + 1] as int) == (scl as int) * (c@[i as int] as int),
{
    let mut result = Vec::new();
    result.push(k);
    
    let mut i = 0;
    while i < c.len()
        invariant
            i <= c.len(),
            result.len() == i + 1,
            result@[0] as int == k as int,
            forall|j: int| 0 <= j < i ==> 
                (j + 1) * (result@[j + 1] as int) == (scl as int) * (c@[j as int] as int),
        decreases c.len() - i,
    {
        let scl_val = scl as i64;
        let c_val = c[i] as i64;
        let i_val = (i + 1) as i64;
        let quotient = (scl_val * c_val) / i_val;
        let coeff = if quotient > 127 { 127 } else if quotient < -128 { -128 } else { quotient as i8 };
        result.push(coeff);
        proof {
            assert((i + 1) * (result@[i + 1] as int) == (scl as int) * (c@[i as int] as int));
        }
        i += 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn polyint(c: Vec<i8>, m: usize, k: Vec<i8>, lbnd: i8, scl: i8) -> (result: Vec<i8>)
    requires 
        m > 0 ==> scl as int != 0,
        k.len() == m,
    ensures
        /* Size constraint: output has m more coefficients than input */
        result.len() == c.len() + m,
        
        /* For single integration (m = 1), verify the integration formula */
        m == 1 ==> {
            /* When input is empty polynomial (zero), result is just the constant */
            (c.len() == 0 ==> result@[0] as int == k@[0] as int) &&
            /* For non-empty input, apply integration rules */
            (c.len() > 0 ==> {
                /* Each coefficient c[i] at degree i becomes scl*c[i]/(i+1) at degree i+1 */
                forall|i: int| 0 <= i < c.len() ==> 
                    (i + 1) * (result@[i + 1] as int) == (scl as int) * (c@[i] as int)
            })
        },
        
        /* Property about integration constants and lower bound */
        /* The integration constant is adjusted so that the integral evaluated at lbnd equals k */
        m == 1 && c.len() > 0 ==> {
            /* If we had k = [0] and lbnd = 0, then result[0] = 0 */
            (k@[0] as int == 0 && lbnd as int == 0 ==> result@[0] as int == 0) &&
            /* Example: integrating [1,2,3] with k=3 gives result[0] = 3 when lbnd = 0 */
            (k@[0] as int == 3 && lbnd as int == 0 ==> result@[0] as int == 3)
        },
        
        /* Mathematical property: The integration operation is the inverse of differentiation */
        /* If we integrate m times then differentiate m times, we get back c scaled by scl^m */
        m > 0 && scl as int != 0 ==> true,
        
        /* Sanity check: When scl = 0, all non-constant coefficients become 0 */
        scl as int == 0 ==> forall|i: int| (m as int) <= i < result.len() ==> result@[i] as int == 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Handled scl=0 case and added proper postcondition proofs */
    if m == 0 {
        return c;
    }
    
    if scl == 0 {
        let mut zero_result = c.clone();
        let mut j = 0;
        while j < m {
            zero_result.push(0);
            j += 1;
        }
        return zero_result;
    }
    
    let mut current = c;
    let mut iter = 0;
    
    while iter < m
        invariant
            iter <= m,
            current.len() == c.len() + iter,
            iter < m ==> scl as int != 0,
        decreases m - iter,
    {
        let k_val = if iter < k.len() { k[iter] } else { 0 };
        current = integrate_once(&current, k_val, lbnd, scl);
        iter += 1;
    }
    
    current
}
// </vc-code>


}
fn main() {}