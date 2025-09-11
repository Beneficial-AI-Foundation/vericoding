use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn numpy_std(a: Vec<f32>, ddof: usize) -> (result: f32)
    requires 
        a.len() > 0,
        ddof < a.len(),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}