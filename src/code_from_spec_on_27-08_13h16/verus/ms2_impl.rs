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
    sum[0] = 0;
    let mut i: usize = 0;
    while i < N
        invariant
            i <= N,
            sum.len() == 1,
            sum[0] <= i,
        decreases
            N - i
    {
        if sum[0] < N {
            sum[0] = sum[0] + 1;
        }
        i = i + 1;
    }
}
// </vc-code>

}

fn main() {}