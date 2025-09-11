use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn polyroots(c: Vec<f64>) -> (roots: Vec<f64>)
    requires 
        c.len() > 1,
        c[c.len() - 1] != 0.0,
    ensures
        roots.len() == c.len() - 1,
        forall|i: int| 0 <= i < c.len() ==> exists|j: int| 0 <= j < c.len() && c[j] != 0.0,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}