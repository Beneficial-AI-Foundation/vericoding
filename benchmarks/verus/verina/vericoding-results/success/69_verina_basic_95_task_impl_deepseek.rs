// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn swap_spec(arr: Seq<i32>, i: int, j: int) -> (result: Seq<i32>)
    requires
        0 <= i < arr.len(),
        0 <= j < arr.len(),
    ensures
        result.len() == arr.len(),
        result[i] == arr[j],
        result[j] == arr[i],
        forall|k: int| 0 <= k < arr.len() && k != i && k != j ==> result[k] == arr[k],
{
    let mut result = arr;
    result = result.update(i, arr[j]);
    result = result.update(j, arr[i]);
    result
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
{
    /* code modified by LLM (iteration 2): manual swap implementation to avoid &mut parameter issues */
    let mut result = arr.clone();
    let temp = result[i];
    result[i] = result[j];
    result[j] = temp;
    result
}
// </vc-code>

}
fn main() {}