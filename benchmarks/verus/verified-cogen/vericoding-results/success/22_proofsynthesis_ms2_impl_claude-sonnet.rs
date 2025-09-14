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
    let mut total: usize = 0;
    let mut i: usize = 0;
    
    while i < N
        invariant
            i <= N,
            total <= i,
            a.len() == N,
            sum.len() == 1,
        decreases N - i
    {
        if a[i] == 1 {
            total = total + 1;
        }
        i = i + 1;
    }
    
    sum.set(0, total);
}
// </vc-code>

}
fn main() {}