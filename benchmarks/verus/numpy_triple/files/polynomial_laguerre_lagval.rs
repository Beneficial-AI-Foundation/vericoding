use vstd::prelude::*;

verus! {

fn lagval(x: Vec<f64>, c: Vec<f64>) -> (result: Vec<f64>)
    requires 
        c.len() > 0,
        x.len() > 0,
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            exists|val: f64| result[i] == val
        },
{
    assume(false);
    unreached()
}

}
fn main() {}