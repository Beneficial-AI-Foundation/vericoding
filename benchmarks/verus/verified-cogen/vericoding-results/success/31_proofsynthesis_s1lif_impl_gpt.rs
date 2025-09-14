// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): lemma to show doubling small i32 values is within range and equals addition */
proof fn lemma_i32_double_safe(n: i32)
    requires
        0 <= n,
        n < 1000
    ensures
        (n as int) + (n as int) <= i32::MAX as int,
        (n as int) + (n as int) >= i32::MIN as int,
        (2 as int) * (n as int) <= i32::MAX as int,
        (2 as int) * (n as int) >= i32::MIN as int,
        n + n == 2 * n
{
    assert((n as int) <= 999);
    assert((n as int) + (n as int) <= 1998);
    assert((n as int) + (n as int) >= 0);
    assert((2 as int) * (n as int) == (n as int) + (n as int));
    assert((i32::MAX as int) >= 1998);
    assert((i32::MIN as int) <= 0);
}
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)

	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,

	ensures
		sum[0] == 2 * N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): compute 2*N safely using a lemma and store it as the single element in sum */
    proof {
        assert(N > 0);
        assert(N < 1000);
        lemma_i32_double_safe(N);
    }
    sum.clear();
    let two_n: i32 = N + N;
    sum.push(two_n);
    proof {
        assert(N + N == 2 * N);
    }
}
// </vc-code>

}
fn main() {}