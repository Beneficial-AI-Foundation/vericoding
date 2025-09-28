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
    /* code modified by LLM (iteration 5): fix bounds checking and add proof assertions */
    let mut result = Vec::new();
    let target_len = arr.len();
    let mut i = 0;
    while i < target_len
        invariant
            i <= target_len,
            result.len() == i,
            forall|k: int| 0 <= k < i && k != index1 ==> result[k] == arr[k],
            target_len == arr.len(),
        decreases target_len - i
    {
        if i == index1 {
            let mut inner_vec = Vec::new();
            let inner_len = arr[i].len();
            let mut j = 0;
            while j < inner_len
                invariant
                    j <= inner_len,
                    inner_vec.len() == j,
                    inner_len == arr[i].len(),
                    i == index1,
                    i < arr.len(),
                    forall|k: int| 0 <= k < j && k != index2 ==> inner_vec[k] == arr[i][k],
                decreases inner_len - j
            {
                if j == index2 {
                    inner_vec.push(val);
                } else {
                    inner_vec.push(arr[i][j]);
                }
                j += 1;
            }
            result.push(inner_vec);
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