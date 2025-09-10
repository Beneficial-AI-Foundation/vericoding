use vstd::prelude::*;

verus! {

fn is_greater(arr: &Vec<i32>, number: i32) -> (result: bool)

    ensures
        result == (forall|i: int| 0 <= i < arr.len() ==> number > arr[i]),
{
    assume(false);
    unreached()
}

}
fn main() {}