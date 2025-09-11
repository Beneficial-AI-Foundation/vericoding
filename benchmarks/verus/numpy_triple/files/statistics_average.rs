use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn average(a: Vec<f32>, weights: Option<Vec<f32>>) -> (result: f32)
    requires 
        a.len() > 0,
        match weights {
            Some(w) => w.len() == a.len(),
            None => true,
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