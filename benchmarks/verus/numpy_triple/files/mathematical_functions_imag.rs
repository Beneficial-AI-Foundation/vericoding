use vstd::prelude::*;

verus! {

fn imag(val: Vec<(f64, f64)>) -> (result: Vec<f64>)
    ensures
        result.len() == val.len(),
        forall|i: int| 0 <= i < val.len() ==> result[i] == val[i].1,
        forall|i: int| 0 <= i < val.len() ==> (val[i].1 == 0.0 ==> result[i] == 0.0),
        forall|i: int| 0 <= i < val.len() ==> (val[i].0 != 0.0 || val[i].1 != 0.0 ==> result[i] == val[i].1),
{
    assume(false);
    unreached();
}

}
fn main() {}