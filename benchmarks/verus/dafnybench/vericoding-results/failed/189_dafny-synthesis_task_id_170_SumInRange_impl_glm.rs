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
proof fn sum_to_iterative_step(a: Seq<int>, start: int, i: int)
    requires
        0 <= start <= i < a.len(),
    ensures
        sum_to(a, start, i+1) == sum_to(a, start, i) + a[i]
{
    assert(sum_to(a, start, i+1) == sum_to(a, start, i) + a[i]);
}

proof fn sum_to_seq_eq(a: Seq<int>, start: int, end: int, b: Seq<int>)
    requires
        0 <= start <= end <= a.len(),
        0 <= start <= end <= b.len(),
        forall|i: int| start <= i < end ==> a[i] == b[i],
    ensures
        sum_to(a, start, end) == sum_to(b, start, end)
    decreases end
{
    if start == end {
    } else {
        sum_to_seq_eq(a, start, end - 1, b);
        assert(a[end - 1] == b[end - 1]);
    }
}

proof fn sum_to_map_eq(a: Seq<i32>, start: int, end: int)
    requires
        0 <= start <= end <= a.len(),
    ensures
        sum_to(a.map(|i: int, v: i32| v as int), start, end) == sum_to(a.map(|i: int, v: i32| v as int), start, end)
{
    // Trivial equality, needed for type conversion
}

proof fn sum_to_map_len(a: Seq<i32>)
    ensures
        a.map(|i: int, v: i32| v as int).len() == a.len()
{
    assert forall|i: int| 0 <= i < a.len() implies #[trigger] (a.map(|i: int, v: i32| v as int))[i] == (a[i] as int) by {
        assert(a.map(|_i: int, v: i32| v as int)[i] == (a[i] as int));
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
    let mut s: int = 0;
    let mut i = start;
    
    proof {
        sum_to_map_len(a@);
    }
    
    while i < end
        invariant
            start <= i <= end,
            s == sum_to(a@.map(|i: int, v: i32| v as int), start as int, i as int)
        decreases (end - i) as int
    {
        proof {
            sum_to_iterative_step(a@.map(|i: int, v: i32| v as int), start as int, i as int);
        }
        s = s + (a[i] as int);
        i = i + 1;
    }
    
    s as i32
}
// </vc-code>

fn main() {
}

}