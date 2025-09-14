// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_to(arr: Seq<i64>) -> (result: int)
    decreases arr.len(),
{
    if arr.len() == 0 {
        0
    } else {
        sum_to(arr.drop_last()) + arr.last()
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn sum_range_list(arr: &Vec<i64>, start: usize, end: usize) -> (sum: i128)

    requires
        0 <= start <= end,
        start <= end < arr.len(),

    ensures
        sum_to(arr@.subrange(start as int, end + 1 as int)) == sum,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed arithmetic overflow/underflow, array out of bounds, and subrange specification issues. */
{
    let mut i = start;
    let mut sum: i128 = 0;

    while i <= end
        invariant
            start <= i <= end + 1,
            i <= arr@.len(),
            sum == sum_to(arr@.subrange(start as int, i as int)),
        decreases (end + 1) - i,
    {
        sum = sum + arr[i] as i128;
        i = i + 1;
    }
    sum
}
// </vc-code>

}
fn main() {}