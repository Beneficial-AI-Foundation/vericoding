use vstd::prelude::*;

verus!{

// <vc-helpers>
// No changes needed in helpers for this fix
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32) 
	// pre-conditions-start
	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,
		N < 1000,
	// pre-conditions-end
	// post-conditions-start
	ensures
		sum[0] <= 3 * N,
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
            sum[0] <= 3 * i,
        decreases N - i
    {
        let current_sum = sum[0];
        // Ensure no overflow by checking bounds
        if current_sum <= i32::MAX - 3 {
            sum.set(0, current_sum + 3);
        } else {
            sum.set(0, current_sum);
        }
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}