// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed `ext_equal` from helper (no verification is needed outside the `vc-code` block itself) */
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
/* code modified by LLM (iteration 5): fixed comparison errors inside proof block */
{
    let mut new_arr = arr.clone();
    let mut row_to_modify = new_arr[index1 as int].clone(); // Clone the row to modify

    // Proof for postcondition 1: result.len() == arr.len()
    proof {
        assert(new_arr.len() == arr.len());
    }

    // Proof for postcondition 2: forall|i: int| 0 <= i < arr.len() && i != index1 ==> result[i] == arr[i]
    proof {
        assert forall|i: int| 0 <= i < arr.len() && i != index1 ==> new_arr[i] == arr[i] by {
            // new_arr is a clone, so elements at un-modified indices are the same
        }
    }

    row_to_modify.set(index2 as int, val); // Modify the element within the cloned row

    new_arr.set(index1 as int, row_to_modify); // Update the new_arr with the modified row

    // Proof for postcondition 3: forall|j: int| 0 <= j < arr[index1 as int].len() && j != index2 ==> result[index1 as int][j] == arr[index1 as int][j]
    proof {
        assert forall|j: int| 0 <= j < arr[index1 as int].len() && j != index2 as int ==> new_arr[index1 as int][j] == arr[index1 as int][j] by {
            assert(new_arr[index1 as int][j] == row_to_modify[j]);
            assert(row_to_modify[j] == arr[index1 as int][j]);
        }
    }

    // Proof for postcondition 4: result[index1 as int][index2 as int] == val
    proof {
        assert(new_arr[index1 as int][index2 as int] == val);
    }

    new_arr
}
// </vc-code>

}
fn main() {}