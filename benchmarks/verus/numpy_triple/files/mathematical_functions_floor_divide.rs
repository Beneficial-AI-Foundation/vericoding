use vstd::prelude::*;

verus! {

spec fn floor_div_prop(x: f64, y: f64) -> bool {
    y != 0.0
}

fn numpy_floor_divide(x1: Vec<f64>, x2: Vec<f64>) -> (result: Vec<f64>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2.len() ==> x2[i] != 0.0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> {

            floor_div_prop(x1[i], x2[i])
        },
{
    assume(false);
    unreached();
}

}
fn main() {}