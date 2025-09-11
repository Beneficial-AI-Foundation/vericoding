use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn lagcompanion(c: Vec<f64>) -> (result: Vec<Vec<f64>>)
    requires 
        c.len() >= 2,
    ensures 
        result@.len() == c@.len() - 1,
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == c@.len() - 1,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}