use vstd::prelude::*;

verus! {

fn atleast_1d(arr: Vec<f64>) -> (result: Vec<f64>)
    ensures
        result == arr,
        forall|i: int| 0 <= i < arr.len() ==> result[i] == arr[i],
{
    assume(false);
    unreached();
}

}
fn main() {}