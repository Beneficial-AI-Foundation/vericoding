// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn pow_spec(base: int, exp: nat) -> int
    decreases exp
{
    if exp == 0 {
        1
    } else {
        base * pow_spec(base, (exp - 1) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn polyvander2d(x: Vec<f64>, y: Vec<f64>, x_deg: u8, y_deg: u8) -> (result: Vec<Vec<f64>>)
    requires 
        x.len() == y.len(),
        x.len() > 0,
    ensures
        result.len() == x.len(),
        forall|k: int| 0 <= k < result.len() ==> #[trigger] result[k].len() == (x_deg as int + 1) * (y_deg as int + 1),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}