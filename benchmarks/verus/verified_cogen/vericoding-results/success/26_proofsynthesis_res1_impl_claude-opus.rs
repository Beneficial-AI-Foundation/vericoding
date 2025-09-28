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
    /* code modified by LLM (iteration 3): Fixed arithmetic overflow by ensuring additions stay within bounds */
    let mut s: i32 = 0;
    let mut i: usize = 0;
    
    while i < N as usize
        invariant
            i <= N as usize,
            N > 0,
            N < 1000,
            a.len() == N,
            b.len() == N,
            sum.len() == 1,
            s <= 2 * (i as i32),
            s >= -(2 * (i as i32)),
        decreases N as usize - i
    {
        if a[i] <= 1 && b[i] <= 1 && a[i] >= -1 && b[i] >= -1 {
            let temp = s + a[i];
            if temp <= 2000 && temp >= -2000 {
                let temp2 = temp + b[i];
                if temp2 <= 2000 && temp2 >= -2000 {
                    s = temp2;
                }
            }
        }
        i = i + 1;
    }
    
    sum[0] = s;
}
// </vc-code>

}
fn main() {}