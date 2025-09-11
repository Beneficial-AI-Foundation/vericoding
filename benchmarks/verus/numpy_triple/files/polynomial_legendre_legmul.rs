use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn legmul(c1: Vec<f32>, c2: Vec<f32>) -> (result: Vec<f32>)
    requires 
        c1.len() > 0,
        c2.len() > 0,
    ensures
        result.len() == c1.len() + c2.len() - 1,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}