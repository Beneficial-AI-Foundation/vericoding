use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn cross(a: Vec<f32>, b: Vec<f32>) -> (result: Vec<f32>)
    requires 
        a.len() == 3,
        b.len() == 3,
    ensures 
        result.len() == 3,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}