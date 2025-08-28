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
		sum[0] <= 3 * N,
	// post-conditions-end
// </vc-spec>

// <vc-code>
{
    // impl-start
    let mut total = 0i32;
    let mut i = 0i32;
    while i < N
        invariant
            0 <= i <= N,
            total <= 3 * i,
            total >= 0,
            a.len() == N,
            sum.len() == 1,
            N < 1000,
        decreases N - i
    {
        if a[i as usize] > 0 {
            total = total + 3;
        } else if a[i as usize] < 0 {
            total = total + 2;
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