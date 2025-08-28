use vstd::prelude::*;

verus!{

// <vc-helpers>
// No updates needed for helpers in this case
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
    // Initialize sum[0] to 0
    sum.set(0, 0);

    // Loop to set sum[0] to 6 * N
    let mut i: usize = 0;
    while i < N
        invariant
            i <= N,
            sum.len() == 1,
            sum[0] == 6 * i as i32,
        decreases N - i
    {
        let current_sum = sum[0];
        // Ensure no overflow by using proper type casting and avoiding unnecessary i64
        let new_sum: i32 = current_sum + 6;
        sum.set(0, new_sum);
        i = i + 1;
    }
}
// </vc-code>

}

fn main() {}