use vstd::prelude::*;

verus! {

fn hermint(c: Vec<f32>, m: u32, k: Vec<f32>, lbnd: f32, scl: f32) -> (result: Vec<f32>)
    requires 
        m > 0,
        k.len() == m,
        c.len() > 0,
    ensures 
        result.len() == c.len() + m,
{
    assume(false);
    unreached()
}

}
fn main() {}