use vstd::prelude::*;

verus! {

fn array(data: Vec<f64>) -> (result: Vec<f64>)
    ensures
        result.len() == data.len(),
        forall|i: int| 0 <= i < data.len() ==> result[i] == data[i],
{
    assume(false);
    unreached();
}

}
fn main() {}