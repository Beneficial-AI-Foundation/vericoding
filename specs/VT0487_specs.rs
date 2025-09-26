// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn legder(c: Vec<f64>, m: u8, scl: f64) -> (result: Vec<f64>)
    requires c.len() >= 1,
    ensures
        result.len() == if c.len() > m as usize { c.len() - m as usize } else { 1 },
        m == 0 ==> (result.len() == c.len() && forall|i: int| 0 <= i < c.len() ==> result[i] == c[i]),
        m as usize >= c.len() ==> result.len() == 1,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}