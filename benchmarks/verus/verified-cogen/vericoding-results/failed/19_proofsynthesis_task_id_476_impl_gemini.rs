// <vc-preamble>
#![verifier::loop_isolation(false)]
use vstd::math::*;
use vstd::prelude::*;

verus! {

spec fn max_rcur(seq: Seq<i32>) -> (result:int)
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        max(seq.last() as int, max_rcur(seq.drop_last()))
    }
}

spec fn min_rcur(seq: Seq<i32>) -> (result:int)
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
/* helper modified by LLM (iteration 3): added `decreases` clause to while loop */
fn vec_max(arr: &Vec<i32>) -> (max_val: i32)
    requires arr.len() > 0
    ensures
        max_val == max_rcur(arr@),
        exists|k: int| 0 <= k < arr.len() && arr@[k] == max_val,
{
    let mut max_val = arr[0];
    let mut i: usize = 1;
    while i < arr.len()
        invariant
            arr.len() > 0,
            1 <= i <= arr.len(),
            max_val == max_rcur(arr@.subrange(0, i as int)),
            exists|k: int| 0 <= k < (i as int) && arr@[k] == max_val,
        decreases arr.len() - i
    {
        if arr[i] > max_val {
            max_val = arr[i];
        }
        i = i + 1;
    }
    max_val
}

/* helper modified by LLM (iteration 3): added `decreases` clause to while loop */
fn vec_min(arr: &Vec<i32>) -> (min_val: i32)
    requires arr.len() > 0
    ensures
        min_val == min_rcur(arr@),
        exists|k: int| 0 <= k < arr.len() && arr@[k] == min_val,
{
    let mut min_val = arr[0];
    let mut i: usize = 1;
    while i < arr.len()
        invariant
            arr.len() > 0,
            1 <= i <= arr.len(),
            min_val == min_rcur(arr@.subrange(0, i as int)),
            exists|k: int| 0 <= k < (i as int) && arr@[k] == min_val,
        decreases arr.len() - i
    {
        if arr[i] < min_val {
            min_val = arr[i];
        }
        i = i + 1;
    }
    min_val
}
// </vc-helpers>

// <vc-spec>
fn sum_min_max(arr: &Vec<i32>) -> (sum: i32)

    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,

    ensures
        sum == max_rcur(arr@) + min_rcur(arr@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): No changes necessary, logic is correct */
    let max_val = vec_max(arr);
    let min_val = vec_min(arr);
    max_val + min_val
}

// </vc-code>

}
fn main() {}