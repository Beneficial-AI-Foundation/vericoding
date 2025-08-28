use vstd::prelude::*;

verus!{

// <vc-helpers>
// </vc-helpers>
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
    let mut total: usize = 0;
    let mut i: usize = 0;
    
    while i < N
        invariant
            i <= N,
            i <= a.len(),
            total <= i,
        decreases N - i
    {
        if a[i] > 0 {
            total = total + 1;
        }
        i = i + 1;
    }
    
    sum.set(0, total);
    // impl-end
}
// </vc-code>

}

fn main() {}