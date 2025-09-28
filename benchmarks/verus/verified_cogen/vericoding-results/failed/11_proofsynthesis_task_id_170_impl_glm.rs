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
/* helper modified by LLM (iteration 5): fixed bounds checking in helper function */
proof fn sum_to_subrange_add(arr: Seq<i64>, start: int, i: int)
    requires
        0 <= start <= i < arr.len(),
    ensures
        sum_to(arr.subrange(start, i+1)) == sum_to(arr.subrange(start, i)) + arr[i]
{
    let sub1 = arr.subrange(start, i);
    let sub2 = arr.subrange(start, i+1);
    assert(sub2 == sub1.push(arr[i]));
    assert(sub2.drop_last() == sub1);
    assert(sub2.last() == arr[i]);
}
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
{
    /* code modified by LLM (iteration 5): fixed loop bounds and overflow issues */
    let mut total: i128 = 0;
    let mut i = start;
    while i <= end
        invariant
            start <= i <= end + 1,
            i <= arr.len() as int,
            total == sum_to(arr@.subrange(start as int, i as int))
        decreases
            end - i + 1
    {
        total += arr[i] as i128;
        proof {
            if i < end {
                sum_to_subrange_add(arr@, start as int, i as int);
            }
        }
        i += 1;
    }
    total
}
// </vc-code>

}
fn main() {}