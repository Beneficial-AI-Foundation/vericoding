use vstd::prelude::*;

verus!{

// <vc-helpers>

// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

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
    // impl-start
    sum.set(0, 0);
    // impl-end
}
// </vc-code>

}

fn main() {}