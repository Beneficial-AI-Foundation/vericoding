use vstd::prelude::*;

verus! {

fn trimcoef(c: Vec<f32>, tol: f32) -> (result: Vec<f32>)
    ensures
        result.len() >= 1,
        result.len() <= c.len(),
{
    assume(false);
    unreached()
}

}
fn main() {}