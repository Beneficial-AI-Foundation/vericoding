use vstd::prelude::*;

verus! {

fn numpy_std(a: Vec<f32>, ddof: usize) -> (result: f32)
    requires 
        a.len() > 0,
        ddof < a.len(),
{
    assume(false);
    unreached()
}

}
fn main() {}