// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): lemma to bound 2*(i+1) within i32 using n < 1000 */
proof fn lemma_step_safe(i: nat, n: nat)
    requires
        i < n,
        n < 1000
    ensures
        0 <= 2 * ((i + 1) as int),
        2 * ((i + 1) as int) <= i32::MAX as int
{
    assert(i + 1 <= n);
    assert(((i + 1) as int) <= (n as int));
    assert(n <= 999);
    assert((n as int) <= 999);
    assert(2 * ((i + 1) as int) <= 2 * (n as int));
    assert(2 * (n as int) <= 2 * 999);
    assert(2 * 999 == 1998);
    assert(1998 <= i32::MAX as int);
    assert(0 <= 2 * ((i + 1) as int));
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
		sum[0] == 2 * N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): implemented counted loop with invariant sum[0] == 2*i and used helper lemma for overflow safety */
    let n = N;
    let mut i: usize = 0;
    sum[0] = 0;
    while i < n
        invariant
            i <= n,
            n == N,
            n < 1000,
            sum.len() == 1,
            sum[0] as int == 2 * (i as int)
        decreases n - i
    {
        proof {
            lemma_step_safe(i as nat, n as nat);
            assert((sum[0] as int) + 2 == 2 * ((i + 1) as int));
            assert(2 * ((i + 1) as int) <= i32::MAX as int);
            assert(i32::MIN as int <= 0);
            assert(0 <= 2 * ((i + 1) as int));
            assert(i32::MIN as int <= (sum[0] as int) + 2);
        }
        sum[0] = sum[0] + 2;
        i += 1;
    }
    proof {
        assert(i == n);
        assert(n == N);
    }
}
// </vc-code>

}
fn main() {}