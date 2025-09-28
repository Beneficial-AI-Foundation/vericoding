// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed power function ensures clause by splitting into two implications */
fn integrate_once(c: Vec<i8>, k: i8, lbnd: i8, scl: i8) -> (res: Vec<i8>)
    ensures
        res.len() == c.len() + 1,
        forall|i: int| 0 <= i < c.len() ==> (i+1) * (res@[i+1] as int) == (scl as int) * (c@[i] as int),
{
    let n = c.len();
    let mut res = Vec::new();
    res.push(k);
    if n == 0 {
        return res;
    }
    let mut sum = 0i8;
    for i in 0..n
        invariant
            1 <= res.len() == i + 1,
            sum == (0..i).sum(|j: int| (res@[j+1] as int) * (power(lbnd as int, j+1))),
    {
        let denominator = (i+1) as i8;
        let term = if scl == 0 {
            0i8
        } else {
            (scl * c[i]) / denominator
        };
        res.push(term);
        let p = power(lbnd as int, i+1);
        sum = sum + term * p;
    }
    res[0] = res[0] - sum;
    res
}

/* helper modified by LLM (iteration 5): fixed power function ensures clause by splitting into two implications */
fn power(base: int, exp: int) -> (result: int)
    requires 0 <= exp,
    decreases exp,
    ensures
        exp == 0 ==> result == 1,
        exp > 0 ==> result == base * power(base, exp - 1),
{
    if exp == 0 {
        1
    } else {
        base * power(base, exp - 1)
    }
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
/* code modified by LLM (iteration 5): fixed power function in helpers */
{
    if m == 0 {
        c
    } else {
        let mut result = c;
        let mut j = 0;
        while j < m
            invariant
                0 <= j <= m,
                result.len() == c.len() + j,
        {
            result = integrate_once(result, k[j], lbnd, scl);
            j = j + 1;
        }
        result
    }
}
// </vc-code>


}
fn main() {}