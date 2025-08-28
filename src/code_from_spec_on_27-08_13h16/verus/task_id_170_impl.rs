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
// pure-end

// <vc-helpers>
proof fn sum_to_subrange(arr: Seq<i64>, start: int, end: int)
    requires
        0 <= start <= end,
        end <= arr.len(),
    ensures
        sum_to(arr.subrange(start, end)) == if start == end { 0 } else { arr[start] + sum_to(arr.subrange(start + 1, end)) },
    decreases end - start,
{
    if start == end {
        assert(sum_to(arr.subrange(start, end)) == 0);
    } else {
        sum_to_subrange(arr, start + 1, end);
        assert(sum_to(arr.subrange(start, end)) == arr[start] + sum_to(arr.subrange(start + 1, end)));
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_range_list(arr: &Vec<i64>, start: usize, end: usize) -> (sum: i128)
    // pre-conditions-start
    requires
        0 <= start <= end,
        start <= end < arr.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        sum_to(arr@.subrange(start as int, end + 1 as int)) == sum,
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut sum: i128 = 0;
    let mut i: usize = start;
    while i < end + 1
        invariant
            start <= i <= end + 1,
            0 <= start <= end < arr.len(),
            sum == sum_to(arr@.subrange(start as int, i as int)),
        decreases end - i + 1,
    {
        sum = sum + arr[i] as i128;
        i = i + 1;
    }
    sum
}
// </vc-code>

} // verus!

fn main() {}