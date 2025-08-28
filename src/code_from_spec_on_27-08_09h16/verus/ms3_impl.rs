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
		sum[0] <= 2 * N,
	// post-conditions-end
// </vc-spec>

// <vc-code>
{
    // impl-start
    let mut total: i32 = 0;
    let mut i: i32 = 0;
    while i < N
        invariant
            0 <= i <= N,
            total <= 2 * i,
            a.len() == N,
            sum.len() == 1,
            total <= 2 * N,
            N < 1000,
        decreases N - i,
    {
        if a[i as usize] > 0 {
            if total < 2 * N && total + 1 <= 2 * N {
                total += 1;
            }
        } else {
            if total < 2 * N && total + 1 <= 2 * N {
                total += 1;
            }
        }
        i += 1;
    }
    sum.set(0, total);
    // impl-end
}
// </vc-code>

}
fn main() {}