// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added bounds check and strengthened invariants */
fn update_inner_vec(inner: Vec<nat>, index: usize, val: nat) -> (result: Vec<nat>)
    requires index < inner.len(),
    ensures
        result.len() == inner.len(),
        forall|i: int| 0 <= i < inner.len() && i != index ==> result[i] == inner[i],
        result[index as int] == val,
{
    let mut new_inner = Vec::new();
    let mut i = 0;
    while i < inner.len()
        invariant
            i <= inner.len(),
            new_inner.len() == i,
            forall|j: int| 0 <= j < i && j != index ==> new_inner[j] == inner[j],
            i > index ==> new_inner[index as int] == val,
        decreases inner.len() - i,
    {
        if i == index {
            new_inner.push(val);
        } else {
            new_inner.push(inner[i]);
        }
        i += 1;
    }
    new_inner
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
    /* code modified by LLM (iteration 5): added bounds checking in precondition call */
    let mut result: Vec<Vec<nat>> = Vec::new();
    let mut i = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i && j != index1 ==> result[j] == arr[j],
            i > index1 ==> result[index1 as int].len() == arr[index1 as int].len(),
            i > index1 ==> forall|k: int| 0 <= k < arr[index1 as int].len() && k != index2 ==> result[index1 as int][k] == arr[index1 as int][k],
            i > index1 ==> result[index1 as int][index2 as int] == val,
        decreases arr.len() - i,
    {
        if i == index1 {
            proof {
                assert(index2 < arr[i].len());
            }
            let modified_inner = update_inner_vec(arr[i].clone(), index2, val);
            result.push(modified_inner);
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