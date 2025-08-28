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
    let mut total = 0;
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == N,
            sum.len() == 1,
            N > 0,
            total <= i,
        decreases a.len() - i,
    {
        if a[i] == 1 {
            total += 1;
        }
        i += 1;
    }
    sum.set(0, total);
    // impl-end
}
// </vc-code>

}

fn main() {}