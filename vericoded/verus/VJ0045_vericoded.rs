// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): bound 3*n by i32::MAX for n < 1000 */
proof fn lemma_three_times_n_bounded_by_i32_max(n: nat)
    requires
        n < 1000,
    ensures
        3 * n <= i32::MAX as int
{
    assert(n <= 999);
    assert(3 * n <= 3 * 999);
    assert(3 * 999 == 2997);
    assert(2997 <= i32::MAX as int);
}

/* helper modified by LLM (iteration 4): trivial fact that i32::MIN <= 0 */
proof fn lemma_i32_min_le_zero()
    ensures
        i32::MIN as int <= 0
{
}
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: usize)

	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,

	ensures
		sum[0] == 3 * N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): carry 3*N<=i32::MAX as loop invariant to use inside the loop */
    assert(sum.len() == 1);
    sum[0] = 0;
    proof { lemma_three_times_n_bounded_by_i32_max(N as nat); }
    let mut i: usize = 0;
    while i < N
        invariant
            i <= N,
            sum.len() == 1,
            sum[0] as int == 3 * (i as int),
            0 <= sum[0] as int,
            3 * (N as nat) <= i32::MAX as int,
        decreases N - i
    {
        assert(i < N);
        assert(i + 1 <= N);
        assert(((i + 1) as int) <= (N as nat));
        assert((sum[0] as int) + 3 == 3 * ((i + 1) as int));
        assert(3 * ((i + 1) as int) <= 3 * (N as nat));
        assert((sum[0] as int) + 3 <= i32::MAX as int);
        proof { lemma_i32_min_le_zero(); }
        assert(0 <= (sum[0] as int) + 3);
        assert(i32::MIN as int <= (sum[0] as int) + 3);
        sum[0] = sum[0] + 3;
        i += 1;
    }
}
// </vc-code>

}
fn main() {}