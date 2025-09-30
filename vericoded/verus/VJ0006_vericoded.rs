// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
fn set_sum_to_zero(sum: &mut Vec<i32>)
    ensures
        sum.len() == 1,
        sum[0] == 0
{
    sum.clear();
    sum.push(0);
}

proof fn lemma_pos_5N(N: i32)
    requires
        N > 0,
        N < 1000
    ensures
        0 <= 5 * N
{
}
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32) 

	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,
		N < 1000,

	ensures
		sum[0] <= 5 * N,
// </vc-spec>
// <vc-code>
{
    set_sum_to_zero(sum);
    proof { lemma_pos_5N(N); }
    assert(sum[0] <= 5 * N);
}
// </vc-code>

}
fn main() {}