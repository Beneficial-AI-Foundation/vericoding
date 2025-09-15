// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): identity helper for nat */
spec fn nat_identity(n: nat) -> nat { n }
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
    /* code modified by LLM (iteration 5): build result by iterating rows and replacing specified element */
    let mut result: Vec<Vec<nat>> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant i <= arr.len() && result.len() == i && forall|k: int| 0 <= k && k < i as int && k != index1 as int ==> result[k as usize] == arr[k as usize]
        decreases arr.len() - i
    {
        if i == index1 {
            let mut new_row: Vec<nat> = Vec::new();
            let mut j: usize = 0;
            while j < arr[i].len()
                invariant j <= arr[i].len() && new_row.len() == j && forall|l: int| 0 <= l && l < j as int && l != index2 as int ==> new_row[l as usize] == arr[i][l as usize]
                decreases arr[i].len() - j
            {
                if j == index2 {
                    new_row.push(val);
                } else {
                    new_row.push(arr[i][j]);
                }
                j += 1;
            }
            result.push(new_row);
        } else {
            result.push(arr[i].clone());
        }
        i += 1;
    }
    proof {
        assert(result.len() == arr.len());
        assert(forall|ii: int| 0 <= ii && ii < arr.len() as int && ii != index1 as int ==> result[ii as usize] == arr[ii as usize]);
        assert(forall|jj: int| 0 <= jj && jj < arr[index1].len() as int && jj != index2 as int ==> result[index1][jj as usize] == arr[index1][jj as usize]);
        assert(result[index1][index2] == val);
    }
    result
}
// </vc-code>

}
fn main() {}