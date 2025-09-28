use vstd::prelude::*;

verus! {

spec fn sum_to(a: Seq<int>, start: int, end: int) -> int
    recommends 
        0 <= start <= end <= a.len(),
    decreases end
    when 0 <= start <= end <= a.len()
{
    if start == end {
        0
    } else {
        sum_to(a, start, end - 1) + a[end - 1]
    }
}

// <vc-helpers>
fn int_sum_to(a: Seq<int>, start: int, end: int) -> int
    recommends
        0 <= start <= end,
        end <= a.len(),
    decreases end - start
{
    if start == end {
        0
    } else {
        int_sum_to(a, start, (end - 1) as int) + a[(end - 1) as int]
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_in_range(a: &[i32], start: usize, end: usize) -> (sum: i32)
    requires 
        start <= end <= a.len(),
    ensures
        sum == sum_to(a@.map(|i, v| v as int), start as int, end as int),
// </vc-spec>
// <vc-code>
{
    let mut sum: i32 = 0;
    let mut i: usize = start;

    while i < end
        invariant
            start <= i,
            i <= end,
            sum as int == int_sum_to(a@.map(|idx, val| val as int), start as int, i as int),
    {
        sum = sum + a[i];
        i = i + 1;
    }
    sum
}
// </vc-code>

fn main() {
}

}