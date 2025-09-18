// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Removed `old` from primitive type arguments in pre/post conditions. */
fn swap_in_place(arr: &mut Vec<i32>, i: usize, j: usize)
    requires
        i < old(arr).len(),
        j < old(arr).len(),
    ensures
        arr.len() == old(arr).len(),
        arr[i as int] == old(arr)[j as int],
        arr[j as int] == old(arr)[i as int],
        forall|k: int| 0 <= k < old(arr).len() && k != i && k != j ==> arr[k] == old(arr)[k],
{
    let val_i = arr[i];
    let val_j = arr[j];
    arr.set(i, val_j);
    arr.set(j, val_i);
}
// </vc-helpers>

// <vc-spec>
fn swap(arr: &Vec<i32>, i: usize, j: usize) -> (result: Vec<i32>)
    requires
        i < arr.len(),
        j < arr.len(),
    ensures
        result.len() == arr.len(),
        result[i as int] == arr[j as int],
        result[j as int] == arr[i as int],
        forall|k: int| 0 <= k < arr.len() && k != i && k != j ==> result[k] == arr[k],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): The code logic was already correct in the previous turn. */
{
    let mut result = arr.clone();
    let val_i = arr[i];
    let val_j = arr[j];
    result.set(i, val_j);
    result.set(j, val_i);
    result
}
// </vc-code>

}
fn main() {}