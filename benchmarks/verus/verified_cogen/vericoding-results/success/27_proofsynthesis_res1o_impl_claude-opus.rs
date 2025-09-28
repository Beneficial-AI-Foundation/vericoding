// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)

	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
		old(sum).len() == 1,
		N < 1000,

	ensures
		sum[0] <= 2 * N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Added overflow checks and refined invariants */
    let mut total: i32 = 0;
    let mut i: usize = 0;
    
    while i < N as usize
        invariant
            i <= N as usize,
            a.len() == N,
            b.len() == N,
            sum.len() == 1,
            N > 0,
            N < 1000,
            total >= 0,
            total <= 2 * (i as i32),
            i <= 1000,
        decreases N as usize - i,
    {
        let a_val = a[i];
        let b_val = b[i];
        
        if a_val <= 1 && b_val <= 1 && a_val >= 0 && b_val >= 0 {
            if total + a_val <= 2000 && total + a_val + b_val <= 2000 {
                total = total + a_val + b_val;
            } else {
                total = total + 2;
            }
        } else if a_val <= 1 && a_val >= 0 {
            if total + a_val + 1 <= 2000 {
                total = total + a_val + 1;
            } else {
                total = total + 2;
            }
        } else if b_val <= 1 && b_val >= 0 {
            if total + 1 + b_val <= 2000 {
                total = total + 1 + b_val;
            } else {
                total = total + 2;
            }
        } else {
            total = total + 2;
        }
        
        i = i + 1;
    }
    
    sum[0] = total;
}
// </vc-code>

}
fn main() {}