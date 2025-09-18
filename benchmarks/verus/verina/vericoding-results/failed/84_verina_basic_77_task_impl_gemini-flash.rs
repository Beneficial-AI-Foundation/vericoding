// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Cast `usize` to `int` for return type to resolve type mismatch and ensure correct comparison in `ensures` clause. */
fn get_row_len(arr: &Vec<Vec<nat>>, index: usize) -> (result: int)
    requires
        (index as int) < arr.len(),
    ensures
        result == arr[index].len() as int
{
    arr[index].len() as int
}
// </vc-helpers>

// <vc-spec>
fn modify_array_element(arr: Vec<Vec<nat>>, index1: usize, index2: usize, val: nat) -> (result: Vec<Vec<nat>>)
    requires
        index1 < arr.len(),
        index2 < arr[index1 as int].len(),
    ensures
        result.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() && i != index1 ==> result[i] == arr[i],
        forall|j: int| 0 <= j < arr[index1 as int].len() && j != index2 ==> result[index1 as int][j] == arr[index1 as int][j],
        result[index1 as int][index2 as int] == val,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Implemented core logic for `modify_array_element`, ensuring safe updates and correct indexing. */
{
    let mut new_arr = arr.clone();
    let mut new_row = new_arr.index(index1);
    new_row.set(index2, val);
    new_arr.set(index1, new_row);
    new_arr
}
// </vc-code>

}
fn main() {}