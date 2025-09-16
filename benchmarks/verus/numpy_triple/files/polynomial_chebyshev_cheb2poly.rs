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

        true, // Polynomial relationship holds for all x (simplified)

        (c.len() == 4 ==>
            (c[0] == 0.0 && c[1] == 1.0 && c[2] == 2.0 && c[3] == 3.0) ==>
            (p[0] == -2.0 && p[1] == -8.0 && p[2] == 4.0 && p[3] == 12.0)),

        true, // Polynomial transformation property (simplified)

        true  // Polynomial approximation property (simplified)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}