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
		sum[0] <= N,
	// post-conditions-end
// </vc-spec>

// <vc-code>
{
    // impl-start
    sum.set(0, 0);
    let mut i = 0;
    while i < N
        invariant
            i <= N,
            sum.len() == 1,
            sum[0] <= i,
        decreases N - i,
    {
        let current_sum = sum[0];
        if current_sum < N {
            sum.set(0, current_sum + 1);
        }
        i += 1;
    }
    // impl-end
}
// </vc-code>

}

fn main() {}