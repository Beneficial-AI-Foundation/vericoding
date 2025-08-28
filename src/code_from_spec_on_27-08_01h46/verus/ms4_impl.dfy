use vstd::prelude::*;

verus!{

// <vc-helpers>
spec fn nat_from_i32(x: i32) -> nat {
    if x >= 0 { x as nat } else { 0 }
}
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
		sum[0] <= 3 * N,
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
            total <= 3 * N,
            i <= a@.len(),
            N == a@.len(),
        decreases N - i,
    {
        if a[i as usize] > 0 {
            let old_total = total;
            if a[i as usize] <= 3 * N && total <= 3 * N - a[i as usize] {
                total = total + a[i as usize];
            } else {
                total = 3 * N;
            }
        }
        if total > 3 * N {
            total = 3 * N;
        }
        i += 1;
    }
    sum.set(0, total);
    // impl-end
}
// </vc-code>

}
fn main() {}