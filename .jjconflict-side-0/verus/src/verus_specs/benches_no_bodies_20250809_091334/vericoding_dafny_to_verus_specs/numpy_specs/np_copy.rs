use vstd::prelude::*;

verus! {

// SPEC
fn copy(arr: &Vec<i32>) -> (ret: Vec<i32>)
    ensures
        ret.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> ret[i] == arr[i],
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

fn main() {}

}