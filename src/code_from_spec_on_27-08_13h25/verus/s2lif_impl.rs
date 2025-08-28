use vstd::prelude::*;

verus!{

// <vc-helpers>
// No updates needed for helpers section as the issues are fixed in the code section
// </vc-helpers>

// <vc-spec>
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
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
    sum[0] = 0; // Initialize sum[0] to 0 to satisfy invariant before loop
    let mut i: i32 = 0;
    while i < N
        invariant
            0 <= i <= N,
            sum.len() == 1,
            sum[0] == 3 * i,
        decreases
            N - i
    {
        let old_sum = sum[0];
        sum[0] = old_sum + 3; // Avoid overflow by ensuring N < 1000 in precondition
        i = i + 1;
        assert(sum[0] == 3 * i); // Ensure invariant holds at the end of loop body
    }
}
// </vc-code>

}

fn main() {}