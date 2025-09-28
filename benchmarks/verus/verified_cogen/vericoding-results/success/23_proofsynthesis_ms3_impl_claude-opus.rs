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
		sum[0] <= 2 * N,
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
            total <= 2 * (i as i32),
            N > 0,
            N < 1000,
            i <= 1000,
            total <= 2000,
        decreases a.len() - i
    {
        if a[i] <= 2 {
            if total <= 2000 - 2 {
                total = total + if a[i] >= 0 { if a[i] <= 2 { a[i] } else { 2 } } else { 0 };
            }
        } else {
            if total <= 2000 - 2 {
                total = total + 2;
            }
        }
        i = i + 1;
    }
    
    sum[0] = total;
}
// </vc-code>

}
fn main() {}