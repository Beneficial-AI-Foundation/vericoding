use vstd::prelude::*;


verus!{

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	// pre-conditions-start
	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
		old(sum).len() == 1,
        N < 1000,
	// pre-conditions-end
	// post-conditions-start
	ensures
		sum[0] <= 2 * N,
	// post-conditions-end
// </vc-spec>

// <vc-code>
{
    // impl-start
    let mut total = 0i32;
    let mut i = 0;
    
    while i < N
        invariant
            0 <= i <= N,
            total <= 2 * i,
            N > 0,
            N < 1000,
            a.len() == N,
            b.len() == N,
            sum.len() == 1,
        decreases N - i,
    {
        if a[i as usize] > b[i as usize] {
            total = total + 1;
        } else {
            total = total + 1;
        }
        i = i + 1;
    }
    
    sum[0] = total;
    // impl-end
}
// </vc-code>

}

fn main() {}