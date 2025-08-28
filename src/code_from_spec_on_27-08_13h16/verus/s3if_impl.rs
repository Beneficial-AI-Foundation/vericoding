use vstd::prelude::*;


verus!{

// <vc-helpers>
// No updates needed for helpers
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
        sum[0] == 3 * N,
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut i: i32 = 0;
    sum.set(0, 0);
    
    while i < N
        invariant
            0 <= i <= N,
            sum.len() == 1,
            sum[0] == 3 * i,
        decreases N - i
    {
        let current_sum = sum[0];
        proof {
            assert(current_sum == 3 * i);
            assert(i < N);
            assert(3 * i + 3 == 3 * (i + 1));
        }
        // Check for potential overflow before addition
        proof {
            assert(i < N);
            assert(N < 1000);
            assert(3 * i + 3 <= 3 * N);
            assert(3 * N < 3 * 1000);
            assert(3 * 1000 < i32::MAX);
        }
        let new_sum: i32 = current_sum + 3;
        sum.set(0, new_sum);
        i = i + 1;
    }
}
// </vc-code>

}

fn main() {}