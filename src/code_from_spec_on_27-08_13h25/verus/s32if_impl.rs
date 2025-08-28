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
		sum[0] == 4 * N,
	// post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut i: usize = 0;
    sum[0] = 0;
    
    while i < N
        invariant
            i <= N,
            sum.len() == 1,
            sum[0] == 4 * i as i32,
        decreases N - i
    {
        sum[0] = sum[0] + 4;
        i = i + 1;
    }
}
// </vc-code>

}

fn main() {}