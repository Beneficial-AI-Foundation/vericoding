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
proof fn lemma_sum_to_unfold(a: Seq<int>, start: int, end: int)
    requires
        0 <= start <= end <= a.len(),
    ensures
        if start == end {
            sum_to(a, start, end) == 0
        } else {
            sum_to(a, start, end) == sum_to(a, start, end - 1) + a[end - 1]
        },
    decreases end
{
    if start == end {
        assert(sum_to(a, start, end) == 0);
    } else {
        assert(sum_to(a, start, end) == sum_to(a, start, end - 1) + a[end - 1]);
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
    let mut s: i32 = 0;
    let mut i: usize = start;

    proof {
        lemma_sum_to_unfold(a@.map(|j, v| v as int), start as int, start as int);
    }

    while i < end
        invariant
            start <= i <= end,
            end <= a.len(),
            0 <= start as int <= i as int <= end as int <= a@.len(),
            s as int == sum_to(a@.map(|j, v| v as int), start as int, i as int)
        decreases end as int - i as int
    {
        proof {
            assert(i < end);
            assert(i < a.len());
            assert(end <= a.len());
            assert(end as int <= a@.len());
            assert(start as int <= i as int);
            assert(start as int < (i as int) + 1);
            lemma_sum_to_unfold(a@.map(|j, v| v as int), start as int, (i as int) + 1);
            assert((a@.map(|j, v| v as int))[(i as int)] == (a@[i as int
// </vc-code>

fn main() {
}

}