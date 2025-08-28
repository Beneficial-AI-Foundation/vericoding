use vstd::prelude::*;

verus!{

// <vc-helpers>
// No updates needed for helpers
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
    let mut i: i32 = 0;
    let mut local_sum: i32 = 0;

    while i < N
        invariant
            0 <= i <= N,
            local_sum <= 2 * i,
        decreases N - i
    {
        if (i as usize) < a.len() && a[i as usize] > 0 {
            if local_sum < 2 * N && local_sum + 1 <= 2 * N {
                local_sum = local_sum + 1;
            }
        }
        if (i as usize) < b.len() && b[i as usize] > 0 {
            if local_sum < 2 * N && local_sum + 1 <= 2 * N {
                local_sum = local_sum + 1;
            }
        }
        i = i + 1;
    }

    sum[0] = local_sum;
}
// </vc-code>

}

fn main() {}