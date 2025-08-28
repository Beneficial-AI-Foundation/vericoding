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
proof fn sum_to_empty(a: Seq<int>, start: int)
    requires 0 <= start <= a.len()
    ensures sum_to(a, start, start) == 0
{
}

proof fn sum_to_single(a: Seq<int>, start: int)
    requires 0 <= start < a.len()
    ensures sum_to(a, start, start + 1) == a[start]
{
    assert(sum_to(a, start, start + 1) == sum_to(a, start, start) + a[start]);
    assert(sum_to(a, start, start) == 0);
}

proof fn sum_to_extend(a: Seq<int>, start: int, end: int)
    requires 0 <= start < end <= a.len()
    ensures sum_to(a, start, end) == sum_to(a, start, end - 1) + a[end - 1]
{
}

proof fn sum_to_step(a: Seq<int>, start: int, i: int)
    requires 0 <= start <= i < a.len()
    ensures sum_to(a, start, i + 1) == sum_to(a, start, i) + a[i]
{
    sum_to_extend(a, start, i + 1);
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
{
    let mut sum = 0i32;
    let mut i = start;
    
    while i < end
        invariant 
            start <= i <= end <= a.len(),
            sum == sum_to(a@.map(|j, v| v as int), start as int, i as int),
        decreases end - i
    {
        proof {
            sum_to_step(a@.map(|j, v| v as int), start as int, i as int);
            assert(sum_to(a@.map(|j, v| v as int), start as int, (i + 1) as int) == 
                   sum_to(a@.map(|j, v| v as int), start as int, i as int) + 
                   a@.map(|j, v| v as int)[i as int]);
            assert(a@.map(|j, v| v as int)[i as int] == a[i] as int);
        }
        sum = sum + (a[i] as i32);
        i = i + 1;
    }
    
    sum
}
// </vc-code>

fn main() {
}

}