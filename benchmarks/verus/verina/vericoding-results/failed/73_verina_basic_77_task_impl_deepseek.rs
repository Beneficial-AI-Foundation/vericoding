// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn modify_array_element_helper(arr: Vec<Vec<nat>>, index1: usize, index2: usize, val: nat) -> (result: Vec<Vec<nat>>)
    requires
        index1 < arr.len(),
        index2 < arr[index1 as int].len(),
    ensures
        result.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() && i != index1 ==> result[i] == arr[i],
        forall|j: int| 0 <= j < arr[index1 as int].len() && j != index2 ==> result[index1 as int][j] == arr[index1 as int][j],
        result[index1 as int][index2 as int] == val,
{
    /* helper modified by LLM (iteration 5): Use Vec::set instead of update method */
    let mut result = arr;
    let inner_vec = result[index1 as int].clone();
    let updated_inner = inner_vec.set(index2 as int, val);
    result = result.set(index1 as int, updated_inner);
    result
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
{
    /* code modified by LLM (iteration 5): Use Vec::set instead of update method */
    let mut result = arr;
    let inner_vec = result[index1].clone();
    let updated_inner = inner_vec.set(index2, val);
    result = result.set(index1, updated_inner);
    result
}
// </vc-code>

}
fn main() {}