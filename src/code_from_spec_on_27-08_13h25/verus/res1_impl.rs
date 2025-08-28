use vstd::prelude::*;


verus!{

// <vc-helpers>
// No changes needed in helpers for this fix
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
    let mut i: usize = 0;
    sum.set(0, 0);
    
    while i < N as usize
        invariant
            0 <= i <= N as usize,
            i <= N,
            sum.len() == 1,
            sum[0] <= 2 * i as i32,
            i < a.len(),
            i < b.len(),
        decreases
            N as usize - i,
    {
        let a_val = a[i];
        let b_val = b[i];
        let current_sum = sum[0];
        let increment = (if a_val > 0 { 1i32 } else { 0i32 }) + (if b_val > 0 { 1i32 } else { 0i32 });
        sum.set(0, current_sum + increment);
        i = i + 1;
    }
}
// </vc-code>

}

fn main() {}