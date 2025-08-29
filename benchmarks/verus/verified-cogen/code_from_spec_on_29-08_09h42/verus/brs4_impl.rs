use vstd::prelude::*;

verus!{

// <vc-helpers>
fn arithmetic_safe(n: i32, a: i32) -> bool {
    n >= 0 && a >= 0 && 4 * n >= a
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
		sum[0] <= 4 * N,
	// post-conditions-end
// </vc-spec>

// <vc-code>
{
    // impl-start
    let mut total = 0;
    let mut i = 0;
    /* code modified by LLM (iteration 5): cast N to nat for safe arithmetic operations */
    while i < N
        invariant
            0 <= i <= N,
            total <= 4 * i,
            a.len() == N,
            sum.len() == 1,
            i <= a.len() as i32,
        decreases N - i,
    {
        if i < a.len() as i32 && a[i as usize] > 0 {
            /* code modified by LLM (iteration 5): use safe arithmetic with bounds checking */
            let n_as_nat = N as nat;
            let a_val = a[i as usize];
            if a_val >= 0 && total <= 4 * N - a_val {
                total += a_val;
            } else {
                total = 4 * N;
            }
        }
        if total > 4 * N {
            total = 4 * N;
        }
        i += 1;
    }
    sum[0] = total;
    // impl-end
}
// </vc-code>

}

fn main() {}