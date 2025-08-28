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
		sum[0] <= 4 * N,
	// post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut i: i32 = 0;
    let mut temp_sum: i32 = 0;
    while i < N
        invariant
            0 <= i <= N,
            sum.len() == 1,
            temp_sum <= 4 * i,
        decreases N - i
    {
        // Prevent overflow by ensuring temp_sum stays within bounds
        if temp_sum <= i32::MAX - 4 {
            temp_sum = temp_sum + 4;
        } else {
            temp_sum = i32::MAX;
        }
        i = i + 1;
    }
    sum.set(0, temp_sum);
}
// </vc-code>

}

fn main() {}