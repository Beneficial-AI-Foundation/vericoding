use vstd::prelude::*;

verus! {

fn nditer(arr: Vec<f32>) -> (iter: (usize, Vec<f32>))
    ensures
        iter.0 == 0,
        iter.1@ == arr@,
        iter.0 <= arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> iter.1[i] == arr[i]
{
    assume(false);
    unreached();
}

}
fn main() {}