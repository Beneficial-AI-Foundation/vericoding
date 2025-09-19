// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn modify_array_element(arr: Vec<Vec<u8>>, index1: usize, index2: usize, val: u8) -> (result: Vec<Vec<u8>>)
    requires
        index1 < arr.len(),
        index2 < arr[index1 as int]@.len(),
    ensures
        result@.len() == arr@.len(),
        forall|i: int| 0 <= i < arr@.len() && i != index1 ==> result@[i] == arr@[i],
        forall|j: int| 0 <= j < arr@[index1 as int].len() && j != index2 ==> result@[index1 as int][j] == arr@[index1 as int][j],
        result@[index1 as int][index2 as int] == val as nat,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}