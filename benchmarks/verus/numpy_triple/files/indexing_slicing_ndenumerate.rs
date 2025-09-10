use vstd::prelude::*;

verus! {

fn ndenumerate(arr: Vec<f32>) -> (result: Vec<(usize, f32)>)
    ensures 
        result.len() == arr.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].0 == i && result[i].1 == arr[i]
{
    assume(false);
    unreached()
}

}
fn main() {}