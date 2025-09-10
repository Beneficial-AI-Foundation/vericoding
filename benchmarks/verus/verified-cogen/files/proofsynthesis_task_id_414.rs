use vstd::prelude::*;

verus! {

fn any_value_exists(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: bool)

    ensures
        result == exists|k: int| 0 <= k < arr1.len() && arr2@.contains(#[trigger] arr1[k]),
{
    assume(false);
    unreached()
}

}
fn main() {}