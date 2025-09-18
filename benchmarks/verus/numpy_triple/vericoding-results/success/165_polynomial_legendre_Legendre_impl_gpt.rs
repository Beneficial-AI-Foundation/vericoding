// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_standard_interval(r: [f64; 2]) -> bool { r[0] == -1.0 && r[1] == 1.0 }
proof fn lemma_standard_interval_reflexive(r: [f64; 2]) ensures is_standard_interval(r) ==> is_standard_interval(r) { }
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
        result.coef.len() == coef.len(),
        forall|i: int| 0 <= i < coef.len() ==> result.coef[i] == coef[i],
        result.domain == domain,
        result.window == window,
        result.symbol == symbol,
        domain[0] == -1.0 && domain[1] == 1.0 ==> result.domain[0] == -1.0 && result.domain[1] == 1.0,
        window[0] == -1.0 && window[1] == 1.0 ==> result.window[0] == -1.0 && result.window[1] == 1.0,
// </vc-spec>
// <vc-code>
{
    Legendre {
        coef,
        domain,
        window,
        symbol,
    }
}
// </vc-code>

}
fn main() {}