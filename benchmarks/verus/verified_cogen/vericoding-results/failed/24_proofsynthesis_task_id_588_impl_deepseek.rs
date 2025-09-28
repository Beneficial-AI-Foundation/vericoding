// <vc-preamble>
#![verifier::loop_isolation(false)]
use vstd::math::*;
use vstd::prelude::*;

verus! {

spec fn max_rcur(seq: Seq<i32>) -> (result: int)
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        max(seq.last() as int, max_rcur(seq.drop_last()))
    }
}

spec fn min_rcur(seq: Seq<i32>) -> (result: int)
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        min(seq.last() as int, min_rcur(seq.drop_last()))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added decreases clause to resolve verification error */
fn loop_max(arr: &Vec<i32>, idx: usize, current_max: i32) -> (result_max: i32)
    decreases arr.len() - idx,
    requires
        idx <= arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
        current_max >= i32::MIN / 2,
    ensures
        result_max == max(current_max as int, max_rcur(arr@.subrange(idx as int, arr.len() as int))) as i32,
{
    if idx == arr.len() {
        current_max
    } else {
        let new_max = if arr[idx] > current_max { arr[idx] } else { current_max };
        loop_max(arr, idx + 1, new_max)
    }
}

/* helper modified by LLM (iteration 5): Added decreases clause to resolve verification error */
fn loop_min(arr: &Vec<i32>, idx: usize, current_min: i32) -> (result_min: i32)
    decreases arr.len() - idx,
    requires
        idx <= arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
        current_min <= i32::MAX / 2,
    ensures
        result_min == min(current_min as int, min_rcur(arr@.subrange(idx as int, arr.len() as int))) as i32,
{
    if idx == arr.len() {
        current_min
    } else {
        let new_min = if arr[idx] < current_min { arr[idx] } else { current_min };
        loop_min(arr, idx + 1, new_min)
    }
}
// </vc-helpers>

// <vc-spec>
fn difference_max_min(arr: &Vec<i32>) -> (diff: i32)

    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,

    ensures
        diff == max_rcur(arr@) - min_rcur(arr@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): No changes needed to code, helper functions fixed */
{
    let max_val = loop_max(arr, 0, i32::MIN);
    let min_val = loop_min(arr, 0, i32::MAX);
    max_val - min_val
}
// </vc-code>

}
fn main() {}