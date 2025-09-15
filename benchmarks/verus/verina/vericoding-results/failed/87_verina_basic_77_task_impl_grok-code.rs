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
    /* code modified by LLM (iteration 2): removed 'as int' casts to fix compilation errors since nat and int types cannot be used in executable code */
    let mut result = Vec::new();
    for i in 0..arr.len() {
        if i == index1 {
            let mut inner = Vec::new();
            for j in 0..arr[index1].len() {
                if j == index2 {
                    inner.push(val);
                } else {
                    inner.push(arr[index1][j]);
                }
            }
            result.push(inner);
        } else {
            result.push(arr[i].clone());
        }
    }
    result
}
// </vc-code>

}
fn main() {}