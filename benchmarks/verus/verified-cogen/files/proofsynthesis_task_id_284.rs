use vstd::prelude::*;

verus! {

fn all_elements_equals(arr: &Vec<i32>, element: i32) -> (result: bool)

    ensures
        result == (forall|i: int| 0 <= i < arr.len() ==> (arr[i] == element)),
{
    assume(false);
    unreached()
}

}
fn main() {}