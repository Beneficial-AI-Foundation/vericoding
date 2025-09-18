// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    let mut result = arr.clone();
    let mut inner = arr[index1].clone();
    inner.set(index2, val);
    result.set(index1, inner);
    result
}
// </vc-code>

}
fn main() {}