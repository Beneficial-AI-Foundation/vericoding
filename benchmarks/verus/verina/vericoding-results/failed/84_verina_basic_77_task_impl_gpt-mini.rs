// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): construct a new row with element at index2 replaced */
fn modify_row(row: Vec<nat>, index2: usize, val: nat) -> (res: Vec<nat>)
    requires
        index2 < row.len(),
    ensures
        res.len() == row.len(),
        forall|j: int| 0 <= j < row.len() as int && j != index2 as int ==> res[j] == row[j],
        res[index2 as int] == val,
{
    let mut res: Vec<nat> = Vec::new();
    let mut i: usize = 0;
    while i < row.len()
        invariant
            0 <= i as int,
            i <= row.len(),
            res.len() == i,
            forall|k: int| 0 <= k < i as int && k != index2 as int ==> res[k] == row[k],
            forall|k: int| 0 <= k < i as int && k == index2 as int ==> res[k] == val,
        decreases row.len() - i
    {
        if i == index2 {
            res.push(val);
        } else {
            res.push(row[i]);
        }
        i += 1;
    }
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
/* code modified by LLM (iteration 5): iterate rows and replace target row using modify_row */
{
    let mut result: Vec<Vec<nat>> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i as int,
            i <= arr.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i as int && k != index1 as int ==> result[k] == arr[k],
            forall|k: int| 0 <= k < i as int && k == index1 as int ==> result[k] == modify_row(arr[index1].clone(), index2, val),
        decreases arr.len() - i
    {
        if i == index1 {
            let new_row = modify_row(arr[index1].clone(), index2, val);
            result.push(new_row);
        } else {
            result.push(arr[i].clone());
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}