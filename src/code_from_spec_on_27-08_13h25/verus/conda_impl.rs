use vstd::prelude::*;

verus!{

// <vc-helpers>
// No changes needed in helpers for this fix
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
		sum[0] == 2 * N,
	// post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut i: i32 = 0;
    sum[0] = 0;
    while i < N
        invariant
            0 <= i <= N,
            sum.len() == 1,
            sum[0] == 2 * i,
        decreases N - i
    {
        let new_sum: i32 = sum[0] + 2;
        proof {
            assert(sum[0] == 2 * i);
            assert(new_sum == 2 * i + 2);
            assert(new_sum == 2 * (i + 1));
        }
        sum[0] = new_sum;
        i = i + 1;
    }
}
// </vc-code>

}

fn main() {}