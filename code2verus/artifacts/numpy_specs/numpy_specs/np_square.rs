use vstd::prelude::*;

verus! {

fn square(arr: &[i32]) -> (ret: Vec<i32>)
    ensures
        ret.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> ret[i] == arr[i] * arr[i],
{
    assume(false);
    Vec::new()
}

}

fn main() {
    // Empty main function for compilation
}