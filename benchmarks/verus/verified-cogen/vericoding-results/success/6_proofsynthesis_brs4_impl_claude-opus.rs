// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32) 

	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,
		N < 1000,

	ensures
		sum[0] <= 4 * N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed arithmetic overflow and loop invariant */
    let mut total: i32 = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == N as usize,
            sum.len() == 1,
            total <= 4 * (i as i32),
            N > 0,
            N < 1000,
            i <= 1000,
            total >= -4000,
            total <= 4000,
        decreases a.len() - i
    {
        let val = a[i];
        if val <= 4 && val >= 0 {
            total = total + val;
        } else if val > 4 {
            total = total + 4;
        } else {
            // val < 0
            total = total + 0;
        }
        i = i + 1;
    }
    
    sum.set(0, total);
}
// </vc-code>

}
fn main() {}