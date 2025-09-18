// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn update_inner(arr: Vec<Vec<nat>>, i: usize, j: usize, val: nat) -> (result: Vec<Vec<nat>>)
    requires
        i < arr.len(),
        j < arr[i as int].len(),
    ensures
        result.len() == arr.len(),
        forall|k: int| 0 <= k < arr.len() && k != i ==> result[k] == arr[k],
        forall|k: int| 0 <= k < arr[i as int].len() && k != j ==> result[i as int][k] == arr[i as int][k],
        result[i as int][j as int] == val
{
    let mut res = arr;
    let mut row = res[i].clone();
    row.set(j, val);
    res.set(i, row);
    res
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
    update_inner(arr, index1, index2, val)
}
// </vc-code>

}
fn main() {}