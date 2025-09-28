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
		sum[0] <= 3 * N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed arithmetic overflow and invariant */
    let mut total: i32 = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == N as usize,
            sum.len() == 1,
            total <= 3 * (i as i32),
            N > 0,
            N < 1000,
            0 <= i,
            i <= 1000,
            total >= 0,
        decreases a.len() - i
    {
        let val = a[i];
        if val <= 3 {
            if val >= 0 {
                total = total + val;
            } else {
                total = total + 0;
            }
        } else {
            total = total + 3;
        }
        i = i + 1;
    }
    
    sum.set(0, total);
}
// </vc-code>

}
fn main() {}