/* Test element-wise for finiteness (not infinity and not NaN) */

use vstd::prelude::*;

verus! {
fn isfinite(x: &Vec<f64>) -> (result: Vec<bool>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> {
            result[i] == (!x[i].is_infinite() && !x[i].is_nan()) &&
            (result[i] == true <==> x[i].is_finite()) &&
            (result[i] == false <==> (x[i].is_nan() || x[i].is_infinite())) &&
            (x[i] == 0.0 ==> result[i] == true) &&
            (result[i] == true ==> exists|bound: f64| x[i].abs() <= bound) &&
            (result[i] == false ==> (x[i].is_nan() || x[i].is_infinite())) &&
            (result[i] == true ==> !x[i].is_nan() && !x[i].is_infinite())
        }
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}