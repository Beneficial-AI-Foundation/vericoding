use vstd::prelude::*;

verus!{

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, c: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	// pre-conditions-start
	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
		old(c).len() == N,
		old(sum).len() == 1,
		N < 1000,
	// pre-conditions-end
	// post-conditions-start
	ensures
		sum[0] <= 3 * N,
	// post-conditions-end
// </vc-spec>

// <vc-code>
{
    // impl-start
    let mut total: i32 = 0;
    let mut i: usize = 0;
    
    /* code modified by LLM (iteration 5): removed vector element bounds invariants that cannot be proven from preconditions */
    while i < N as usize
        invariant
            i <= N as usize,
            total <= 3 * (i as i32),
            total >= 0,
            a.len() == N,
            b.len() == N,
            c.len() == N,
            sum.len() == 1,
        decreases N as usize - i,
    {
        let elem_sum = a[i] + b[i] + c[i];
        if elem_sum > 0 && total < 1000 {
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