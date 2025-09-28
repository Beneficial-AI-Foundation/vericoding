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
proof fn sum_to_lemma_empty(a: Seq<int>, start: int)
    requires start == 0
    ensures sum_to(a, start, start) == 0
{
}

proof fn sum_to_additive(a: Seq<int>, start: int, mid: int, end: int)
    requires 
        0 <= start <= mid <= end <= a.len(),
    ensures
        sum_to(a, start, end) == sum_to(a, start, mid) + sum_to(a, mid, end),
    decreases end - mid
{
    if mid == end {
        assert(sum_to(a, mid, end) == 0);
    } else {
        sum_to_additive(a, start, mid, end - 1);
        assert(sum_to(a, start, end) == sum_to(a, start, end - 1) + a[end - 1]);
        assert(sum_to(a, start, end - 1) == sum_to(a, start, mid) + sum_to(a, mid, end - 1));
        assert(sum_to(a, mid, end) == sum_to(a, mid, end - 1) + a[end - 1]);
    }
}

proof fn sum_to_step(a: Seq<int>, start: int, i: int)
    requires 
        0 <= start <= i < a.len(),
    ensures
        sum_to(a, start, i + 1) == sum_to(a, start, i) + a[i],
{
    assert(sum_to(a, start, i + 1) == sum_to(a, start, i) + a[i]);
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
    let mut sum = 0i32;
    let mut i = start;
    
    while i < end
        invariant
            start <= i <= end <= a.len(),
            sum == sum_to(a@.map(|j, v| v as int), start as int, i as int),
            sum >= i32::MIN && sum <= i32::MAX,
        decreases end - i
    {
        assert(i < a.len());
        assert(a[i as int] >= i32::MIN && a[i as int] <= i32::MAX);
        
        let old_sum = sum;
        sum = sum + a[i as int];
        
        proof {
            let seq_mapped = a@.map(|j, v| v as int);
            sum_to_step(seq_mapped, start as int, i as int);
            assert(sum_to(seq_mapped, start as int, (i + 1) as int) == 
                   sum_to(seq_mapped, start as int, i as int) + seq_mapped[i as int]);
            assert(seq_mapped[i as int] == a@[i as int] as int);
            assert(seq_mapped[i as int] == a[i as int] as int);
            assert(sum == old_sum + a[i as int]);
            assert(sum as int == old_sum as int + a[i as int] as int);
            assert(old_sum as int == sum_to(seq_mapped, start as int, i as int));
            assert(sum as int == sum_to(seq_mapped, start as int, i as int) + a[i as int] as int);
            assert(sum as int == sum_to(seq_mapped, start as int, (i + 1) as int));
        }
        
        i = i + 1;
    }
    
    sum
}
// </vc-code>

fn main() {
}

}