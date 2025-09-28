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
spec fn sum_from(a: Seq<int>, start: int, end: int) -> int
    recommends
        0 <= start <= end <= a.len(),
    decreases end - start
{
    if start == end {
        0
    } else {
        sum_from(a, start, end - 1) + a[end - 1]
    }
}

proof fn lemma_sum_from_eq_sum_to(a: Seq<int>, start: int, end: int)
    requires
        0 <= start <= end <= a.len(),
    ensures
        sum_from(a, start, end) == sum_to(a, start, end),
    decreases end - start
{
    if start == end {
    } else {
        lemma_sum_from_eq_sum_to(a, start, end - 1);
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
            start <= i <= end,
            (sum as int) == sum_from(a@.map(|i, v| v as int), start as int, i as int),
        decreases (end - i)
    {
        sum = sum + a[i];
        i = i + 1;
    }
    proof {
        lemma_sum_from_eq_sum_to(a@.map(|i, v| v as int), start as int, end as int);
    }
    sum
}
// </vc-code>

fn main() {
}

}