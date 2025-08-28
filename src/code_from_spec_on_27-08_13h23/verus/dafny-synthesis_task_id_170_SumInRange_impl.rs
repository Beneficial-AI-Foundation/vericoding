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
proof fn lemma_sum_to_split(a: Seq<int>, start: int, mid: int, end: int)
    requires
        0 <= start <= mid <= end <= a.len(),
    ensures
        sum_to(a, start, end) == sum_to(a, start, mid) + sum_to(a, mid, end),
    decreases end - start
{
    if start == end {
        assert(sum_to(a, start, mid) == 0);
        assert(sum_to(a, mid, end) == 0);
    } else if mid == end {
        assert(sum_to(a, mid, end) == 0);
    } else if start == mid {
        assert(sum_to(a, start, mid) == 0);
    } else {
        lemma_sum_to_split(a, start, mid, end - 1);
        assert(sum_to(a, start, end) == sum_to(a, start, end - 1) + a[end - 1]);
        assert(sum_to(a, mid, end) == sum_to(a, mid, end - 1) + a[end - 1]);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn sum_in_range(a: &[i32], start: usize, end: usize) -> (sum: i32)
    requires 
        start <= end <= a.len(),
    ensures
        sum == sum_to(a@.map(|i, v| v as int), start as int, end as int),
// </vc-spec>
// </vc-spec>

// <vc-code>
fn sum_in_range(a: &[i32], start: usize, end: usize) -> (sum: i32)
    requires
        start <= end <= a.len(),
    ensures
        sum == sum_to(a@.map(|i, v| v as int), start as int, end as int),
{
    let mut sum = 0;
    let mut i = start;
    while i < end
        invariant
            start <= i <= end,
            sum == sum_to(a@.map(|i, v| v as int), start as int, i as int),
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