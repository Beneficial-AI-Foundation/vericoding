use vstd::prelude::*;

verus!{

// <vc-helpers>
// No updates needed for helpers
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
    let mut i: usize = 0;
    sum[0] = 0;

    while i < N as usize
        invariant
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= 3 * i as i32,
        decreases N as usize - i,
    {
        if i < a.len() && i < b.len() && i < c.len() {
            let old_sum = sum[0];
            sum[0] = old_sum + 1;
            if a[i] > b[i] {
                let old_sum2 = sum[0];
                sum[0] = old_sum2 + 1;
            }
            if a[i] > c[i] {
                let old_sum3 = sum[0];
                sum[0] = old_sum3 + 1;
            }
        }
        i = i + 1;
    }
}
// </vc-code>

}

fn main() {}