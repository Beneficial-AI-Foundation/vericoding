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
/* code modified by LLM (iteration 3): directly compute 3*N safely with proofs since N<1000 prevents overflow */
{
    let val = 3 * N;
    proof {
        assert(val == 3 * N);
        assert( (val as int) == 3 * (N as int) );
    }
    sum[0] = val;
}
// </vc-code>

}
fn main() {}