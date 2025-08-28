use vstd::prelude::*;

verus!{

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	// pre-conditions-start
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
	// pre-conditions-end
	// post-conditions-start
	ensures
		sum[0] == N,
	// post-conditions-end
// </vc-spec>

// <vc-code>
{
    // impl-start
    *sum = vec![N];
    // impl-end
}
// </vc-code>

}

fn main() {}