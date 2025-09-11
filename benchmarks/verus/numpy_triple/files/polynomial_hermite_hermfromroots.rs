use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn hermfromroots(roots: Vec<f64>) -> (coef: Vec<f64>)
    ensures
        coef.len() == roots.len() + 1,
        roots.len() > 0 ==> coef[roots.len() as int] != 0.0,
        forall|i: int| 0 <= i < roots.len() ==> {

            true
        }
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}