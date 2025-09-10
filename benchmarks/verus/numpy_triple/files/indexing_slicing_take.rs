use vstd::prelude::*;

verus! {

fn take(arr: Vec<f32>, indices: Vec<usize>) -> (result: Vec<f32>)
    requires
        forall|i: int| 0 <= i < indices.len() ==> indices[i] < arr.len(),
    ensures
        result.len() == indices.len(),
        forall|i: int| 0 <= i < indices.len() ==> result[i] == arr[indices[i] as int],
{
    assume(false);
    unreached();
}

}
fn main() {}