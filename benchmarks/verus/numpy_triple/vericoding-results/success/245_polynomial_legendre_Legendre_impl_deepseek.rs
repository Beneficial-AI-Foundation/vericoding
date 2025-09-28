// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn mk_legendre_helper(coef: Vec<f64>, domain: [f64; 2], window: [f64; 2], symbol: String) -> Legendre {
    Legendre {
        coef,
        domain,
        window,
        symbol,
    }
}
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
    /* code modified by LLM (iteration 2): Direct struct construction to satisfy postconditions */
    let result = Legendre {
        coef,
        domain,
        window,
        symbol,
    };
    result
}
// </vc-code>

}
fn main() {}