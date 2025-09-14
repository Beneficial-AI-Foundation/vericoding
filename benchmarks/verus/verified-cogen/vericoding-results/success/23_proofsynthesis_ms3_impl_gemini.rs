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
    /* code modified by LLM (iteration 2): added decreases clause to the loop */
    let mut i: i32 = 0;
    let mut total: i32 = 0;
    while i < N
        invariant
            0 <= i <= N,
            a.len() == N,
            sum.len() == 1,
            total == i,
            forall|k: int| 0 <= k < i ==> a@[k] == 1,
        decreases N - i
    {
        a.set(i as usize, 1);
        total = total + a[i as usize];
        i = i + 1;
    }
    sum.set(0, total);
}
// </vc-code>

}
fn main() {}