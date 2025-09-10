use vstd::prelude::*;

verus! {

fn hermfromroots(roots: Vec<f64>) -> (coef: Vec<f64>)
    ensures
        coef.len() == roots.len() + 1,
        roots.len() > 0 ==> coef[roots.len() as int] != 0.0,
        forall|i: int| 0 <= i < roots.len() ==> {

            true
        }
{
    assume(false);
    unreached()
}

}
fn main() {}