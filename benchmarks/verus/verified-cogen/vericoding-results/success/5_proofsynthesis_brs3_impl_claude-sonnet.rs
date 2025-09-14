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
    /* code modified by LLM (iteration 4): use nat types to avoid overflow and ensure bounds */
    let mut total: i32 = 0;
    let mut i: i32 = 0;
    while i < N
        invariant
            0 <= i <= N,
            total <= 3 * i,
            total >= 0,
            i <= a.len(),
            N == a.len(),
            N < 1000,
        decreases N - i
    {
        if i < N && a[i as usize] > 0 {
            total = total + 3;
        }
        i = i + 1;
    }
    sum[0] = total;
}
// </vc-code>

}
fn main() {}