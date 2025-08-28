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
		sum[0] == 6 * N,
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
            sum[0] == 6 * i,
        decreases
            N - i,
    {
        i = i + 1;
        sum[0] = 6 * i;
    }
}
// </vc-code>

}

fn main() {}