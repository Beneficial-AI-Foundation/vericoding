// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): add bounds predicate and lemma ensuring N+2 fits in i32 */
spec fn in_bounds(k: int, n: int) -> bool { 0 <= k && k < n }

/* helper modified by LLM (iteration 4): lemma to bound i32 addition */
proof fn lemma_add2_within_i32(N: i32)
    requires
        0 < N,
        N < 1000
    ensures
        i32::MIN as int <= (N as int + 2) <= i32::MAX as int
{
    assert(N as int + 2 >= 0);
    assert(i32::MIN as int <= 0);
    assert(N as int + 2 <= 1002);
    assert(1002 <= i32::MAX as int);
}
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)

	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
		old(sum).len() == 1,
		N < 1000,

	ensures
		forall |k:int| 0 <= k < N ==> b[k] == N + 2,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fill b with N+2, prove no overflow and postcondition */
    let n = b.len();

    proof { lemma_add2_within_i32(N); }
    let val: i32 = N + 2;
    assert(val == N + 2);

    // From the precondition old(b).len() == N and no length changes, we can equate current length to N
    proof { assert(b.len() as int == N as int); }

    let mut i: usize = 0;
    while i < n
        invariant
            b.len() == n,
            0 <= i as int <= n as int,
            forall |k:int| 0 <= k < i as int ==> b@[k] == val,
            val == N + 2
        decreases n - i
    {
        assert(i < b.len());
        b[i] = val;
        assert(b@[i as int] == val);
        i += 1;
    }

    assert(i == n);
    assert(forall |k:int| 0 <= k < n as int ==> b@[k] == val);

    // Relate n and N (needed for the postcondition range)
    proof { assert(n as int == N as int); }
}
// </vc-code>

}
fn main() {}