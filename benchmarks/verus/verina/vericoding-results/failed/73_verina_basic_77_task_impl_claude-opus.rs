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
    /* code modified by LLM (iteration 3): Fixed type mismatches by casting index1 to int for array indexing */
    let mut result = arr;
    let mut inner = result[index1].clone();
    assert(inner.len() == result[index1 as int].len());
    assert(forall|j: int| 0 <= j < inner.len() ==> inner[j] == result[index1 as int][j]);
    inner.set(index2, val);
    assert(inner[index2 as int] == val);
    assert(forall|j: int| 0 <= j < inner.len() && j != index2 as int ==> inner[j] == result[index1 as int][j]);
    result.set(index1, inner);
    assert(result[index1 as int][index2 as int] == val);
    assert(forall|j: int| 0 <= j < result[index1 as int].len() && j != index2 as int ==> result[index1 as int][j] == arr[index1 as int][j]);
    result
}
// </vc-code>

}
fn main() {}