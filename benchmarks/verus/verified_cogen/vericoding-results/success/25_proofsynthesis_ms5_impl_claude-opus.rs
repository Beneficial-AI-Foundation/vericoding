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
    /* code modified by LLM (iteration 4): Handle negative values properly to maintain invariants */
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
            0 <= i,
            i <= 1000,
            total >= -4 * (i as i32),
        decreases
            a.len() - i,
    {
        let val = a[i];
        let add_val: i32 = if val >= 4 {
            4
        } else if val >= -4 {
            val
        } else {
            -4
        };
        
        proof {
            assert(-4 <= add_val <= 4);
            assert(total <= 4 * (i as i32));
            assert(total >= -4 * (i as i32));
            assert(total + add_val <= 4 * (i as i32) + 4);
            assert(total + add_val >= -4 * (i as i32) - 4);
            assert(4 * (i as i32) + 4 == 4 * ((i + 1) as i32));
            assert(-4 * (i as i32) - 4 == -4 * ((i + 1) as i32));
        }
        
        total = total + add_val;
        i = i + 1;
    }
    
    sum.set(0, total);
}
// </vc-code>

}
fn main() {}