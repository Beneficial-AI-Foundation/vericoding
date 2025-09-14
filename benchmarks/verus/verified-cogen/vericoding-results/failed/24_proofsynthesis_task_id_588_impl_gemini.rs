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
/* helper modified by LLM (iteration 3): confirmed correctness */
proof fn max_min_rcur_inductive(s: Seq<i32>, elem: i32)
    requires s.len() > 0
    ensures
        max_rcur(s.push(elem)) == max(max_rcur(s), elem as int),
        min_rcur(s.push(elem)) == min(min_rcur(s), elem as int),
{}
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
{
    /* code modified by LLM (iteration 5): fixed syntax of invariant block */
    let mut max_val = arr[0];
    let mut min_val = arr[0];
    let mut i: usize = 1;

    while i < arr.len()
        decreases arr.len() - i
        invariant {
            1 <= i <= arr.len(),
            max_val as int == max_rcur(arr@.subrange(0, i as int)),
            min_val as int == min_rcur(arr@.subrange(0, i as int)),
            forall|k: int| 0 <= k < arr.len() ==> i32::MIN / 2 < #[trigger] arr[k] < i32::MAX / 2,
        }
    {
        proof {
            max_min_rcur_inductive(arr@.subrange(0, i as int), arr@[i as int]);
        }

        if arr[i] > max_val {
            max_val = arr[i];
        }

        if arr[i] < min_val {
            min_val = arr[i];
        }
        
        i = i + 1;
    }

    max_val - min_val
}
// </vc-code>

}
fn main() {}