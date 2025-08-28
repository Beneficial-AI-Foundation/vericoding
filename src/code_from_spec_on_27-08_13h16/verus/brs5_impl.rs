use vstd::prelude::*;

verus!{

// <vc-helpers>
// No changes needed in helpers for this fix
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
		sum[0] <= 5 * N,
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
            sum[0] <= 5 * i,
        decreases
            N - i
    {
        let current_sum = sum[0];
        if i < a.len() as i32 {
            let idx = i as usize;
            // Ensure no overflow by checking bounds before addition
            let new_sum = if current_sum <= i32::MAX - a[idx] {
                current_sum + a[idx]
            } else {
                current_sum
            };
            // Ensure no overflow in the comparison
            let threshold = if i <= i32::MAX / 5 {
                5 * i + 5
            } else {
                i32::MAX
            };
            if new_sum <= threshold {
                sum.set(0, new_sum);
            } else {
                sum.set(0, current_sum);
            }
        } else {
            // Ensure no overflow by checking bounds before addition
            let new_sum = if current_sum < i32::MAX {
                current_sum + 1
            } else {
                current_sum
            };
            // Ensure no overflow in the comparison
            let threshold = if i <= i32::MAX / 5 {
                5 * i + 5
            } else {
                i32::MAX
            };
            if new_sum <= threshold {
                sum.set(0, new_sum);
            } else {
                sum.set(0, current_sum);
            }
        }
        i = if i < i32::MAX { i + 1 } else { i };
    }
}
// </vc-code>

}

fn main() {}