use vstd::prelude::*;

verus! {

fn max_difference(arr: &Vec<i32>) -> (diff: i32)

    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,

    ensures
        forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() ==> arr[i] - arr[j] <= diff,
{
    assume(false);
    unreached()
}

}
fn main() {}