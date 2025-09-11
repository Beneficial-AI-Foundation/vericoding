// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn cheb2poly(c: Vec<f64>) -> (p: Vec<f64>)
    ensures

        p.len() == c.len(),

        (c.len() == 0 ==> p@ == c@),
        (c.len() == 1 ==> p@ == c@),
        (c.len() == 2 ==> p@ == c@),

        (forall|x: f64|

            true),

        (c.len() == 4 ==>
            (c[0] == 0.0 && c[1] == 1.0 && c[2] == 2.0 && c[3] == 3.0) ==>
            (p[0] == -2.0 && p[1] == -8.0 && p[2] == 4.0 && p[3] == 12.0)),

        (forall|d: Vec<f64>, alpha: f64, beta: f64|
            d.len() == c.len() ==> true),

        (forall|epsilon: f64, d: Vec<f64>|
            d.len() == c.len() ==> true)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}