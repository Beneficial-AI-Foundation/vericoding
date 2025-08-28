use vstd::prelude::*;

verus!{

// <vc-helpers>
// No updates needed for helpers in this case
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    // pre-conditions-start
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,
    // pre-conditions-end
    // post-conditions-start
    ensures
        sum[0] == 4 * N,
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut i: i32 = 0;
    if sum.len() > 0 {
        sum[0] = 0;
    }
    while i < N
        invariant
            0 <= i <= N,
            sum.len() > 0,
            sum[0] == 4 * i as i32,
        decreases
            N - i
    {
        if sum.len() > 0 {
            let current_sum: i32 = sum[0];
            sum[0] = current_sum + 4;
        }
        i = i + 1;
    }
}
// </vc-code>

}

fn main() {}