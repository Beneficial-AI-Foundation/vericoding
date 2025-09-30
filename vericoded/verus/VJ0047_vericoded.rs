// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fix spec type by casting nat to int */
spec fn five_times(n: nat) -> int { 5 * (n as int) }

/* helper modified by LLM (iteration 3): lemma bounding five_times within i32 */
proof fn lemma_five_times_i32_bound(n: nat)
    requires
        n < 1000
    ensures
        0 <= five_times(n) <= i32::MAX as int
{
    assert(0 <= n as int);
    assert(0 <= five_times(n));
    assert(n as int <= 999);
    assert(5 * (n as int) <= 5 * 999);
    assert(5 * 999 <= i32::MAX as int);
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
		sum[0] == 5 * N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fix arithmetic typing, prove safety, and compute sum[0] = 5*N */
    // Ensure the index 0 is in-bounds
    assert(sum.len() == 1);
    assert(0 < sum.len());

    // Prove cast from usize to i32 is safe using N < 1000
    proof {
        assert(0 <= N as int);
        assert(N < 1000);
        assert(N as int <= 999);
        assert(N as int <= i32::MAX as int);
    }
    let n_i32: i32 = N as i32;
    assert((n_i32 as int) == N as int);

    // Prove the multiplication fits in i32
    proof {
        assert(0 <= n_i32 as int);
        assert(5 * (N as int) <= 5 * 999);
        assert(5 * 999 <= i32::MAX as int);
    }

    // Perform the computation
    sum[0] = 5 * n_i32;

    // Relate the stored value to the postcondition in the mathematical integers
    proof {
        assert((sum[0] as int) == 5 * (n_i32 as int));
        assert(5 * (n_i32 as int) == 5 * (N as int));
    }
}
// </vc-code>

}
fn main() {}