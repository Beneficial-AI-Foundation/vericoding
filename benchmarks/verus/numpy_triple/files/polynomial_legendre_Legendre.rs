use vstd::prelude::*;

verus! {

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
{
    assume(false);
    unreached();
}

}
fn main() {}