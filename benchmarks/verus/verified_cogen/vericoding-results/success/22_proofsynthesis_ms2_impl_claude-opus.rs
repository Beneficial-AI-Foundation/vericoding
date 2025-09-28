// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<usize>, sum: &mut Vec<usize>, N: usize) 

	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,

	ensures
		sum[0] <= N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to fix loop verification */
    let mut count: usize = 0;
    let mut i: usize = 0;
    while i < N
        invariant
            a.len() == N,
            sum.len() == 1,
            i <= N,
            count <= i,
        decreases N - i,
    {
        if i < a.len() && a[i] == 1 {
            count = count + 1;
        }
        i = i + 1;
    }
    sum[0] = count;
}
// </vc-code>

}
fn main() {}