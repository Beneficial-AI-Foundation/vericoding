use vstd::prelude::*;

verus!{

// <vc-helpers>
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
    sum[0] = 0;
    let mut i: i32 = 0;
    while i < N
        invariant
            0 <= i <= N,
            sum.len() == 1,
            sum[0] <= i,
        decreases
            N - i
    {
        sum[0] = sum[0] + 1;
        i = i + 1;
    }
}
// </vc-code>

}

fn main() {}