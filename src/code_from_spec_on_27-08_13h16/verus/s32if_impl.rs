use vstd::prelude::*;

verus!{

// <vc-helpers>
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
		sum[0] == 4 * N,
	// post-conditions-end
// </vc-spec>

// <vc-code>
{
    // Initialize sum[0] to 0 if needed, though not strictly necessary as we will overwrite it
    sum[0] = 0;
    
    // Set sum[0] to 4 * N as per the postcondition
    sum[0] = 4 * N as i32;
    
    // No need to use 'a' since the postcondition does not depend on it
    ()
}
// </vc-code>

}

fn main() {}