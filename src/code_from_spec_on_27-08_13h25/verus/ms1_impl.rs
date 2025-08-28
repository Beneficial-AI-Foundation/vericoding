use vstd::prelude::*;

verus!{

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<usize>, sum: &mut Vec<usize>, N: usize) 
	// pre-conditions-start
	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,
	// pre-conditions-end
	// post-conditions-start
	ensures
		sum[0] == 0,
	// post-conditions-end
// </vc-spec>

// <vc-code>
{
    // impl-start
    sum[0] = 0;
    // impl-end
}
// </vc-code>

}

fn main() {}