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
		sum[0] == 5 * N,
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
            sum[0] == 5 * i,
        decreases N - i
    {
        let current_sum = sum[0];
        // Ensure no overflow by using a safe computation with bounds check
        let new_sum = current_sum as i64 + 5;
        assert(new_sum <= i32::MAX as i64);
        sum.set(0, new_sum as i32);
        i = i + 1;
    }
}
// </vc-code>

}

fn main() {}