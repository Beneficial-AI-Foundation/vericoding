// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed syntax errors including extra parenthesis, incorrect push, and typo in assignment */
fn pow_int(base: i64, exp: usize) -> i64 {
    let mut res = 1i64;
    for _ in 0..exp {
        res = res.wrapping_mul(base);
    }
    res
}

/* helper modified by LLM (iteration 5): Fixed syntax errors in integrate_once: removed extra parenthesis, fixed push syntax, corrected assignment */
fn integrate_once(p: Vec<i8>, scl: i8, lbnd: i8, c_val: i8) -> Vec<i8> {
    let n = p.len();
    let mut result: Vec<i8> = Vec::with_capacity(n + 1);
    result.push(0);
    for i in 0..n {
        proof {
            assert(i < p.len());
        }
        let num: i64 = (scl as i64).wrapping_mul(p[i] as i64);
        let den: i64 = i as i64 + 1;
        #[verifier::truncate] let coeff = (num / den) as i8;
        result.push(coeff);
    }
    let mut sum: i64 = 0;
    let upper = n + 1;
    for i in 1..upper {
        proof {
            assert(i < result.len());
        }
        let coeff = result[i] as i64;
        let pow_val = pow_int(lbnd as i64, i);
        sum = sum.wrapping_add(coeff.wrapping_mul(pow_val));
    }
    let needed_c0: i64 = (c_val as i64).wrapping_add((-1i64).wrapping_mul(sum));
    #[verifier::truncate] result[0] = needed_c0 as i8;
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
/* code modified by LLM (iteration 5): Fixed syntax errors in main code: corrected function call, fixed assertion */
{
    if m == 0 {
        c
    } else {
        let mut result = c;
        let upper = m;
        for i in 0..upper {
            proof {
                assert(i < k.len());
            }
            let const_val = k[i];
            result = integrate_once(result, scl, lbnd, const_val);
        }
        result
    }
}
// </vc-code>


}
fn main() {}