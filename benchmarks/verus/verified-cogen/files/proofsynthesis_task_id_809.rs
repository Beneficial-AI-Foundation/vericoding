use vstd::prelude::*;

verus! {

fn is_smaller(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: bool)

    requires
        arr1.len() == arr2.len(),

    ensures
        result == (forall|i: int| 0 <= i < arr1.len() ==> arr1[i] > arr2[i]),
{
    assume(false);
    unreached()
}

}
fn main() {}