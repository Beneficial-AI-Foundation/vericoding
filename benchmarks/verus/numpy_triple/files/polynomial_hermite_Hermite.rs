use vstd::prelude::*;

verus! {

fn hermite_eval(coef: Vec<f32>, x: f32) -> (result: f32)
    requires coef.len() > 0,
    ensures 
        coef.len() == 1 ==> result == coef[0],
        coef.len() >= 2 ==> true,
{
    assume(false);
    unreached()
}

}
fn main() {}