use vstd::prelude::*;

verus!{

// <vc-helpers>
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
    // impl-start
    let mut total = 0;
    let mut i = 0;
    while i < N
        invariant
            0 <= i <= N,
            total <= 4 * i,
    {
        if a[i as usize] > 0 {
            total += a[i as usize];
        }
        i += 1;
    }
    sum[0] = total;
    // impl-end
}
// </vc-code>

}

fn main() {}