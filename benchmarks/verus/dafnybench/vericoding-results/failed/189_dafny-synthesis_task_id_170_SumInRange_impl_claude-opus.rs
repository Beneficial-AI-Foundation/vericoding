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
proof fn sum_to_extend(a: Seq<int>, start: int, end: int)
    requires
        0 <= start <= end < a.len(),
    ensures
        sum_to(a, start, end + 1) == sum_to(a, start, end) + a[end],
    decreases end - start,
{
    reveal(sum_to);
    if start == end {
        assert(sum_to(a, start, end) == 0);
        assert(sum_to(a, start, end + 1) == a[end]);
    } else {
        assert(sum_to(a, start, end + 1) == sum_to(a, start, end) + a[end]);
    }
}

proof fn sum_to_invariant(a: Seq<int>, start: int, mid: int, end: int, partial_sum: int)
    requires
        0 <= start <= mid <= end <= a.len(),
        partial_sum == sum_to(a, start, mid),
    ensures
        partial_sum + sum_to(a, mid, end) == sum_to(a, start, end),
    decreases end - mid,
{
    reveal(sum_to);
    if mid == end {
        assert(sum_to(a, mid, end) == 0);
        assert(partial_sum + 0 == partial_sum);
        assert(sum_to(a, start, end) == sum_to(a, start, mid));
    } else {
        sum_to_invariant(a, start, mid, end - 1, partial_sum);
        assert(sum_to(a, mid, end) == sum_to(a, mid, end - 1) + a[end - 1]);
        assert(partial_sum + sum_to(a, mid, end - 1) == sum_to(a, start, end - 1));
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
    let mut sum: i32 = 0;
    let mut i: usize = start;
    
    while i < end
        invariant
            start <= i <= end,
            i <= a.len(),
            end <= a.len(),
            sum as int == sum_to(a@.map(|idx: int, v: i32| v as int), start as int, i as int),
        decreases end - i,
    {
        let old_sum = sum;
        let old_i = i;
        
        proof {
            let mapped = a@.map(|idx: int, v: i32| v as int);
            assert(i < a.len());
            assert(mapped[i as int] == a[i as int] as int);
            sum_to_extend(mapped, start as int, i as int);
            assert(sum_to(mapped, start as int, (i + 1) as int) == 
                   sum_to(mapped, start as int, i as int) + mapped[i as int]);
        }
        
        sum = sum + a[i];
        i = i + 1;
        
        proof {
            let mapped = a@.map(|idx: int, v: i32| v as int);
            assert(sum as int == old_sum as int + a[old_i as int] as int);
            assert(sum as int == sum_to(mapped, start as int, old_i as int) + mapped[old_i as int]);
            assert(sum as int == sum_to(mapped, start as int, (old_i + 1) as int));
            assert(i == old_i + 1);
            assert(sum as int == sum_to(mapped, start as int, i as int));
        }
    }
    
    proof {
        let mapped = a@.map(|idx: int, v: i32| v as int);
        assert(i == end);
        assert(sum as int == sum_to(mapped, start as int, end as int));
    }
    
    sum
}
// </vc-code>

fn main() {
}

}