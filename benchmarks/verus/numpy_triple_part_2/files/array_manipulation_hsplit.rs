// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn hsplit(arr: Vec<f32>, k: usize) -> (result: Vec<Vec<f32>>)
    requires 
        k > 0,
        arr.len() % k == 0,
    ensures
        result.len() == k,
        forall|part_idx: int| 0 <= part_idx < k ==> result[part_idx].len() == arr.len() / k,
        forall|part_idx: int, elem_idx: int| 
            0 <= part_idx < k && 0 <= elem_idx < (arr.len() / k) ==>
            #[trigger] result[part_idx][elem_idx] == arr[part_idx * (arr.len() / k) + elem_idx],
        forall|i: int| 0 <= i < arr.len() ==> 
            exists|p: int, e: int| 
                0 <= p < k && 0 <= e < (arr.len() / k) &&
                i == p * (arr.len() / k) + e &&
                #[trigger] arr[i] == result[p][e]
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}