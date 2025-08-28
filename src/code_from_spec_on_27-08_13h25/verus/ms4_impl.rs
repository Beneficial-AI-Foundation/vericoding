use vstd::prelude::*;

verus!{

// <vc-helpers>
// No updates needed in helpers for this fix
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
    let mut i: i32 = 0;
    sum.set(0, 0);
    
    while i < N
        invariant
            0 <= i <= N,
            sum.len() == 1,
            sum[0] <= 3 * i,
        decreases N - i
    {
        let val = if i < a.len() as i32 { a[i as usize] } else { 0 };
        let current_sum = sum[0];
        // Ensure no overflow by using i64 for comparison
        if current_sum < (3i64 * N as i64) as i32 {
            sum.set(0, current_sum + if val > 0 { 1 } else { 0 });
        }
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}