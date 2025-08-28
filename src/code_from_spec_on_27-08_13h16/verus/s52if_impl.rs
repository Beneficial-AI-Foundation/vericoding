use vstd::prelude::*;

verus!{

// <vc-helpers>
// No updates needed for helpers
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: usize)
	// pre-conditions-start
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,
	// pre-conditions-end
	// post-conditions-start
	ensures
		sum[0] == 6 * N,
	// post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut i: usize = 0;
    sum[0] = 0;

    while i < N
        invariant
            i <= N,
            sum.len() == 1,
            sum[0] == 6 * (i as int),
        decreases N - i
    {
        let old_sum = sum[0];
        proof {
            assert(old_sum == 6 * (i as int));
            assert((i + 1) <= N);
            assert(6 * ((i + 1) as int) == old_sum + 6);
        }
        sum[0] = old_sum + 6;
        i = i + 1;
    }
}
// </vc-code>

}

fn main() {}