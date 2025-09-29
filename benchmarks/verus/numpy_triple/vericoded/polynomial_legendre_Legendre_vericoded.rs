// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
struct Legendre {

    coef: Vec<f64>,

    domain: [f64; 2],

    window: [f64; 2],

    symbol: String,
}

fn mk_legendre(
    coef: Vec<f64>,
    domain: [f64; 2],
    window: [f64; 2],
    symbol: String
) -> (result: Legendre)
    ensures
        result.coef@ == coef@,
        result.domain == domain,
        result.window == window,
        result.symbol == symbol,
        domain[0] == -1.0 && domain[1] == 1.0 ==> result.domain[0] == -1.0 && result.domain[1] == 1.0,
        window[0] == -1.0 && window[1] == 1.0 ==> result.window[0] == -1.0 && result.window[1] == 1.0,
// </vc-spec>
// <vc-code>
{
    Legendre { coef, domain, window, symbol }
}
// </vc-code>

}
fn main() {}