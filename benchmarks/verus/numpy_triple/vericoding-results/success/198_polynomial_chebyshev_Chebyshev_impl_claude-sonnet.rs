// <vc-preamble>
use vstd::prelude::*;

verus! {

/* Structure representing a Chebyshev polynomial with coefficients and domain/window mapping */
struct ChebyshevPoly {
    /* Coefficients of the Chebyshev polynomial in increasing degree order */
    coef: Vec<i32>,
    /* Domain interval [domain_min, domain_max] */
    domain_min: i32,
    domain_max: i32,
    /* Window interval [window_min, window_max] */
    window_min: i32,
    window_max: i32,
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn chebyshev(coef: Vec<i8>) -> (result: ChebyshevPoly)
    requires coef.len() > 0,
    ensures
        /* Coefficients are preserved */
        result.coef@.len() == coef@.len(),
        forall|i: int| 0 <= i < coef@.len() ==> result.coef@[i] == coef@[i] as i32,
        /* Default domain is [-1, 1] */
        result.domain_min == -1,
        result.domain_max == 1,
        /* Default window is [-1, 1] */
        result.window_min == -1,
        result.window_max == 1,
        /* Domain interval is valid */
        result.domain_min < result.domain_max,
        /* Window interval is valid */
        result.window_min < result.window_max,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to while loop */
    let mut result_coef: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < coef.len()
        invariant
            i <= coef.len(),
            result_coef@.len() == i,
            forall|j: int| 0 <= j < i ==> result_coef@[j] == coef@[j] as i32,
        decreases coef.len() - i
    {
        result_coef.push(coef[i] as i32);
        i = i + 1;
    }
    
    ChebyshevPoly {
        coef: result_coef,
        domain_min: -1,
        domain_max: 1,
        window_min: -1,
        window_max: 1,
    }
}
// </vc-code>


}
fn main() {}