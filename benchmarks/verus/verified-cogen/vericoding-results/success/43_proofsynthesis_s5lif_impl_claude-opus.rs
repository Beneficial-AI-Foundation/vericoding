// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)

	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,

	ensures
		sum[0] == 6 * N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix arithmetic overflow by using proof block */
    let mut i: i32 = 0;
    sum.set(0, 0);
    
    while i < N
        invariant
            0 <= i <= N,
            a.len() == N,
            sum.len() == 1,
            sum[0] == 6 * i,
            N < 1000,
        decreases N - i,
    {
        proof {
            assert(i < N);
            assert(i < 1000);
            assert(6 * i < 6000);
            assert(6 * i + 6 < 6006);
        }
        let current_sum = sum[0];
        sum.set(0, current_sum + 6);
        i = i + 1;
        proof {
            assert(sum[0] == current_sum + 6);
            assert(current_sum == 6 * (i - 1));
            assert(sum[0] == 6 * (i - 1) + 6);
            assert(sum[0] == 6 * i);
        }
    }
}
// </vc-code>

}
fn main() {}