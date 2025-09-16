// <vc-preamble>
use vstd::prelude::*;

verus! {

#[verifier::memoize]
spec fn spec_fib(n: nat) -> (ret:nat)
    decreases n,
{
    if (n == 0) {
        0
    } else if (n == 1) {
        1
    } else {
        spec_fib((n - 1) as nat) + spec_fib((n - 2) as nat)
    }
}

spec fn inner_expr_fib(n: u32, ret: Option<u32>) -> (result:bool) {
    match ret {
        None => spec_fib(n as nat) > u32::MAX,
        Some(f) => f == spec_fib(n as nat),
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_add_overflow_condition(a: u32, b: u32)
    ensures
        (a > u32::MAX - b) ==> ((a as int) + (b as int) > (u32::MAX as int)),
        (a <= u32::MAX - b) ==> ((a as int) + (b as int) <= (u32::MAX as int)),
        (a > u32::MAX - b) ==> ((a as nat) + (b as nat) > (u32::MAX as nat)),
        (a <= u32::MAX - b) ==> ((a as nat) + (b as nat) <= (u32::MAX as nat)),
{ }

/* helper modified by LLM (iteration 2): corrected spec_fib argument to use nat cast for n-1 */
proof fn lemma_fib_succ(n: nat)
    requires
        n >= 1,
    ensures
        spec_fib(n + 1) == spec_fib(n) + spec_fib((n - 1) as nat),
{ }

/* helper modified by LLM (iteration 2): corrected types in inequality to use spec_fib((k-1) as nat) */
proof fn lemma_fib_step_non_decreasing(k: nat)
    ensures
        spec_fib(k) <= spec_fib(k + 1),
{
    if k == 0 {
        assert(spec_fib(0) <= spec_fib(1));
    } else {
        lemma_fib_succ(k);
        assert(spec_fib(k) <= spec_fib(k) + spec_fib((k - 1) as nat));
    }
}

proof fn lemma_fib_monotonic(m: nat, n: nat)
    requires
        m <= n,
    ensures
        spec_fib(m) <= spec_fib(n),
    decreases n - m,
{
    if m == n {
    } else {
        lemma_fib_step_non_decreasing(m);
        lemma_fib_monotonic(m + 1, n);
    }
}
// </vc-helpers>

// <vc-spec>
fn fib(n: u32) -> (ret: Option<u32>)

    ensures
        inner_expr_fib(n, ret),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fix nat/int casts in invariants and proofs; establish overflow => None and final result equality */
    if n == 0 {
        proof { assert(inner_expr_fib(0u32, Some(0u32))); }
        return Some(0);
    }
    let mut a: u32 = 0;
    let mut b: u32 = 1;
    let mut i: u32 = 1;
    while i < n
        invariant
            i >= 1,
            i <= n,
            (a as nat) == spec_fib((i - 1) as nat),
            (b as nat) == spec_fib(i as nat),
        decreases (n - i) as nat
    {
        if a > u32::MAX - b {
            proof {
                lemma_add_overflow_condition(a, b);
                lemma_fib_succ(i as nat);
                assert(spec_fib((i as nat) + 1) == spec_fib(i as nat) + spec_fib((i - 1) as nat));
                assert(spec_fib((i as nat) + 1) == (b as nat) + (a as nat));
                assert(((a as nat) + (b as nat)) > (u32::MAX as nat));
                assert(spec_fib((i as nat) + 1) > (u32::MAX as nat));
                assert((i as nat) + 1 <= n as nat);
                lemma_fib_monotonic((i as nat) + 1, n as nat);
                assert(spec_fib(n as nat) >= spec_fib((i as nat) + 1));
                assert(spec_fib(n as nat) > (u32::MAX as nat));
            }
            return None;
        }
        let next: u32 = a + b;
        proof {
            lemma_add_overflow_condition(a, b);
            assert(a <= u32::MAX - b);
            assert((next as nat) == (a as nat) + (b as nat));
            lemma_fib_succ(i as nat);
            assert(spec_fib((i as nat) + 1) == spec_fib(i as nat) + spec_fib((i - 1) as nat));
            assert((next as nat) == spec_fib((i as nat) + 1));
        }
        a = b;
        b = next;
        i = i + 1;
    }
    proof {
        assert(i == n);
        assert((b as nat) == spec_fib(n as nat));
    }
    Some(b)
}
// </vc-code>

}
fn main() {}