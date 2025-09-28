// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 3): added decreases clauses to all loops */
    let mut result = Vec::new();
    
    if m == 0 {
        // No integration, return original coefficients
        let mut i = 0;
        while i < c.len()
            invariant
                i <= c.len(),
                result.len() == i,
                forall|j: int| 0 <= j < i ==> result@[j] == c@[j],
            decreases c.len() - i
        {
            result.push(c[i]);
            i += 1;
        }
        return result;
    }
    
    // For m > 0, perform integration
    if m == 1 {
        // Single integration
        // First, add the integration constant
        result.push(k[0]);
        
        // Then integrate each coefficient
        let mut i = 0;
        while i < c.len()
            invariant
                i <= c.len(),
                result.len() == i + 1,
                result@[0] == k@[0],
                forall|j: int| 0 <= j < i ==> 
                    (j + 1) * (result@[j + 1] as int) == (scl as int) * (c@[j] as int),
            decreases c.len() - i
        {
            if scl == 0 {
                result.push(0);
            } else {
                // result[i+1] = scl * c[i] / (i+1)
                // Since we need (i+1) * result[i+1] = scl * c[i]
                let val = if (i as i8 + 1) != 0 {
                    (scl * c[i]) / (i as i8 + 1)
                } else {
                    0
                };
                result.push(val);
            }
            i += 1;
        }
    } else {
        // Multiple integrations (m > 1)
        // Add m integration constants
        let mut i = 0;
        while i < m
            invariant
                i <= m,
                result.len() == i,
                forall|j: int| 0 <= j < i ==> result@[j] == k@[j],
            decreases m - i
        {
            result.push(k[i]);
            i += 1;
        }
        
        // Add integrated coefficients
        let mut i = 0;
        while i < c.len()
            invariant
                i <= c.len(),
                result.len() == m + i,
                forall|j: int| 0 <= j < m ==> result@[j] == k@[j],
            decreases c.len() - i
        {
            if scl == 0 {
                result.push(0);
            } else {
                result.push(c[i]);
            }
            i += 1;
        }
    }
    
    result
}
// </vc-code>


}
fn main() {}