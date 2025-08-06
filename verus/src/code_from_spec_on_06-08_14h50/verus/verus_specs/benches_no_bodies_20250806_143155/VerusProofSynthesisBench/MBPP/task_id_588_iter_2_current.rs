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
// pure-end

spec fn min_rcur(seq: Seq<i32>) -> (result: int)
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        min(seq.last() as int, min_rcur(seq.drop_last()))
    }
}
// pure-end

fn difference_max_min(arr: &Vec<i32>) -> (diff: i32)
    // pre-conditions-start
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        diff == max_rcur(arr@) - min_rcur(arr@),
    // post-conditions-end
{
    let mut max_val = arr[0];
    let mut min_val = arr[0];
    let mut i = 1;
    
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while i < arr.len()
        invariant
            1 <= i <= arr.len(),
            max_val == max_rcur(arr@.subrange(0, i as int)),
            min_val == min_rcur(arr@.subrange(0, i as int)),
            i32::MIN / 2 < max_val < i32::MAX / 2,
            i32::MIN / 2 < min_val < i32::MAX / 2,
        decreases arr.len() - i,
    {
        if arr[i] > max_val {
            max_val = arr[i];
        }
        if arr[i] < min_val {
            min_val = arr[i];
        }
        i += 1;
    }
    
    max_val - min_val
}

} // verus!

fn main() {}