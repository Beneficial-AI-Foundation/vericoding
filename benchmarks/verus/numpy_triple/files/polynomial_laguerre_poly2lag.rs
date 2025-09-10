use vstd::prelude::*;

verus! {

fn poly2lag(pol: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == pol.len(),

        true,
{
    assume(false);
    unreached();
}

}
fn main() {}