use vstd::prelude::*;

verus!{

// <vc-helpers>
spec fn max_3(x: i32) -> i32 {
    if x > 3 { 3 } else { x }
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
    let mut total: i32 = 0;
    let mut i: i32 = 0;
    /* code modified by LLM (iteration 5): removed total >= 0 invariant and simplified overflow checks */
    while i < N
        invariant
            0 <= i <= N,
            total <= 3 * i,
            a.len() == N,
            sum.len() == 1,
        decreases N - i,
    {
        if a[i as usize] > 3 {
            if total <= i32::MAX - 3 {
                total = total + 3;
            }
        } else {
            if a[i as usize] >= 0 && total <= i32::MAX - a[i as usize] {
                total = total + a[i as usize];
            } else if a[i as usize] < 0 && total >= i32::MIN - a[i as usize] {
                total = total + a[i as usize];
            }
        }
        i = i + 1;
    }
    sum.set(0, total);
    // impl-end
}
// </vc-code>

}

fn main() {}