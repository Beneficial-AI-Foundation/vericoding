// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn hermeint(c: Vec<f64>, m: u8, k: Vec<f64>, lbnd: f64, scl: f64) -> (result: Vec<f64>)
    requires 
        scl != 0.0,
        k@.len() == m as int,
    ensures
        result@.len() == c@.len() + m as int,
        scl != 0.0,
        forall|step: int| 0 <= step < m as int ==> #[trigger] k@[step] == k@[step],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}