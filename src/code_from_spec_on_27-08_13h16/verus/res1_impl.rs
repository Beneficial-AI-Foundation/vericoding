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
    sum[0] = 0;
    while i < N as usize
        invariant
            0 <= i <= N as usize,
            i <= N as usize,
            sum[0] <= 2 * i as i32,
            sum[0] >= 0,
            N >= 0,
            a.len() == N as usize,
            b.len() == N as usize,
            sum.len() == 1,
        decreases
            N as usize - i
    {
        if i < a.len() && a[i] > 0 {
            sum[0] = sum[0] + 1;
        }
        if i < b.len() && b[i] > 0 {
            sum[0] = sum[0] + 1;
        }
        i = i + 1;
    }
}
// </vc-code>

}

fn main() {}