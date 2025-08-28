use vstd::prelude::*;

verus!{

// <vc-helpers>
spec fn count_positives(a: Seq<i32>, end: int) -> int
    decreases end
{
    if end <= 0 {
        0
    } else {
        count_positives(a, end - 1) + if a[end - 1] > 0 { 1 } else { 0 }
    }
}

proof fn count_positives_bound(a: Seq<i32>, end: int)
    requires 0 <= end <= a.len()
    ensures count_positives(a, end) <= end
    decreases end
{
    if end > 0 {
        count_positives_bound(a, end - 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    // pre-conditions-start
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        sum[0] <= N,
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut count: i32 = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            0 <= count <= i,
            count <= N,
            i <= N,
            count == count_positives(a@, i as int),
        decreases a.len() - i,
    {
        if a[i] > 0 {
            count = count + 1;
        }
        i += 1;
        
        proof {
            count_positives_bound(a@, i as int);
        }
    }
    sum.set(0, count);
}
// </vc-code>

}

fn main() {}