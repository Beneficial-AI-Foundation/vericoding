// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn fib(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 }
    else if n == 1 { 1 }
    else { fib((n - 1) as nat) + fib((n - 2) as nat) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): this lemma is required for the loop invariant proof */
proof fn fib_sum(n: nat)
    requires n >= 2
    ensures fib(n) == fib((n - 1) as nat) + fib((n - 2) as nat)
{
}

/* helper modified by LLM (iteration 3): proves fib is monotonic to resolve overflow checks */
proof fn fib_monotonic(i: nat, j: nat)
    requires i <= j
    ensures fib(i) <= fib(j)
    decreases j - i
{
    if i < j && j >= 2 {
        fib_monotonic(i, (j - 1) as nat);
    }
}
// </vc-helpers>

// <vc-spec>
fn ComputeFib(n: usize) -> (f: usize)
    ensures f == fib(n as nat)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added an invariant and proof of non-overflow */
    if n == 0 {
        return 0;
    }

    let mut a: usize = 0;
    let mut b: usize = 1;
    let mut i: usize = 1;

    while i < n
        invariant
            1 <= i <= n,
            fib(n as nat) <= usize::MAX,
            a == fib((i - 1) as nat),
            b == fib(i as nat),
        decreases n - i
    {
        proof {
            fib_monotonic((i + 1) as nat, n as nat);
            fib_sum((i + 1) as nat);
        }

        let temp = a + b;
        a = b;
        b = temp;
        i = i + 1;
    }

    b
}
// </vc-code>

}
fn main() {}