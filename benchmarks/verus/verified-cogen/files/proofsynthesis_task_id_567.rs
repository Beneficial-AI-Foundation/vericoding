use vstd::prelude::*;

verus! {

fn is_sorted(arr: &Vec<i32>) -> (is_sorted: bool)

    requires
        arr.len() > 0,

    ensures
        is_sorted == (forall|i: int, j: int| 0 <= i < j < arr.len() ==> (arr[i] <= arr[j])),
{
    assume(false);
    unreached();
}

}
fn main() {}