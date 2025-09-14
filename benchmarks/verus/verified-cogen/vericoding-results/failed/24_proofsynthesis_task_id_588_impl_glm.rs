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
/* code modified by LLM (iteration 5): fix indexing in invariant and remove unnecessary semicolons */
{
    let mut max_val = arr[0];
    let mut min_val = arr[0];
    let mut i = 1;
    while i < arr.len()
        invariant
            1 <= i <= arr.len(),
            forall|j: int| 0 <= j < i ==> min_val <= arr@[j] as int <= max_val,
            max_val == max_rcur(arr@.subrange(0, i as int)),
            min_val == min_rcur(arr@.subrange(0, i as int))
    {
        if arr[i] as int > max_val {
            max_val = arr[i] as int;
        }
        if arr[i] as int < min_val {
            min_val = arr[i] as int;
        }
        i += 1;
    }
    (max_val - min_val) as i32
}
// </vc-code>

}
fn main() {}