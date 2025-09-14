// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)

	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,

	ensures
		sum[0] == N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Use N directly instead of a.len() to avoid casting issues */
    let mut i: i32 = 0;
    let mut total: i32 = 0;
    
    while i < N
        invariant
            0 <= i <= N,
            sum.len() == 1,
            total == i,
        decreases N - i,
    {
        total = total + 1;
        i = i + 1;
    }
    
    proof {
        assert(i == N);
        assert(total == i);
        assert(total == N);
    }
    
    sum.set(0, total);
}
// </vc-code>

}
fn main() {}