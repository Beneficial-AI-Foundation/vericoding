use vstd::prelude::*;

verus! {

spec fn evaluate_laguerre_polynomial<const N: usize>(coef: [f64; N], x: f64) -> f64;

spec fn map_domain(domain: [f64; 2], window: [f64; 2], x: f64) -> f64;

spec fn laguerre_polynomial_basis(n: nat, x: f64) -> f64;

struct Laguerre<const N: usize> {

    coef: [f64; N],

    domain: [f64; 2],

    window: [f64; 2],
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn make_laguerre<const N: usize>(coefficients: [f64; N]) -> (result: Laguerre<N>)
    ensures

        result.coef == coefficients,

        result.domain[0] == 0.0 && result.domain[1] == 1.0,

        result.window[0] == 0.0 && result.window[1] == 1.0,

        forall|x: f64| {
            let transformed_x = map_domain(result.domain, result.window, x);
            exists|value: f64| value == evaluate_laguerre_polynomial(result.coef, transformed_x)
        },

        forall|i: int| 0 <= i < N ==> result.coef[i] == coefficients[i],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}