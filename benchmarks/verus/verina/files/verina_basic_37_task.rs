use vstd::prelude::*;

verus! {

fn find_first_occurrence(arr: &Vec<i32>, target: i32) -> (result: i32)
    requires
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
    ensures
        (result >= 0 ==> {
            &&& 0 <= result < arr.len()
            &&& arr[result as int] == target
            &&& forall|i: int| 0 <= i < result ==> arr[i] != target
        }) &&
        (result == -1 ==> {
            &&& forall|i: int| 0 <= i < arr.len() ==> arr[i] != target
        }),
{
    assume(false);
    unreached()
}

}
fn main() {}