use vstd::prelude::*;

verus! {

// SPEC
fn argmax(arr: &[int]) -> (ret: usize)
    requires 
        arr.len() > 0,
    ensures
        ret < arr.len(),
        forall|i: int| 0 <= i < ret ==> arr[ret as int] > arr[i],
        forall|i: int| ret < i < arr.len() ==> arr[ret as int] >= arr[i],
{
    return 0;  // TODO: Remove this line and implement the function body
}

fn main() {}

}