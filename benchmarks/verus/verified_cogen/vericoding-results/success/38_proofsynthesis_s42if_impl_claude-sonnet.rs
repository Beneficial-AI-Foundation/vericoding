// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: usize)

	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,

	ensures
		sum[0] == 5 * N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix invariant i < 1000 not maintained when i reaches N */
    let mut total: i32 = 0;
    let mut i: usize = 0;
    while i < N
        invariant
            i <= N,
            total == 5 * (i as i32),
            a.len() == N,
            sum.len() == 1,
            i <= N && N < 1000,
            total <= 5000,
        decreases N - i
    {
        i = i + 1;
        total = total + 5;
    }
    sum.set(0, total);
}
// </vc-code>

}
fn main() {}