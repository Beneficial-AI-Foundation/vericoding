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
    /* code modified by LLM (iteration 5): implemented using spec map and Vec::new_from_seq for verifiable construction */
    let result = Vec::new_from_seq(
        &arr.view().map(|i: int, v: Seq<nat>| 
            if i == index1 as int {
                Vec::new_from_seq(
                    &v.map(|j: int, val_old: nat| 
                        if j == index2 as int { val } else { val_old }
                    )
                )
            } else {
                Vec::new_from_seq(&v)
            }
        )
    );
    result
}
// </vc-code>

}
fn main() {}