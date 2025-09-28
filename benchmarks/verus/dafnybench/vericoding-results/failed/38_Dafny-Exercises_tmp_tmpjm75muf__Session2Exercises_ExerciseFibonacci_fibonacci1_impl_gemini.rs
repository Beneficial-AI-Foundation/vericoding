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
/* helper modified by LLM (iteration 2): added lemmas for fib properties */
proof fn fib_add(i: nat)
    ensures fib(i + 2) == fib(i + 1) + fib(i)
{
}

proof fn fib_is_monotonic(i: nat, j: nat)
    requires i <= j
    ensures fib(i) <= fib(j)
{
    if i < j {
        fib_is_monotonic(i, (j - 1) as nat);
        if j >= 2 {
            fib_add((j - 2) as nat);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn fibonacci1(n: u64) -> (f: u64)
    requires n < 100,
    ensures f == fib(n as nat)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): restructured loop to prevent overflow and added proof for invariants */
    if n == 0 {
        return 0;
    }

    let mut a: u64 = 0;
    let mut b: u64 = 1;
    let mut i: u64 = 1;

    while i < n
        invariant
            1 <= i <= n,
            a == fib((i - 1) as nat),
            b == fib(i as nat),
        decreases n - i
    {
        proof {
            if i >= 1 {
                fib_add((i - 1) as nat);
            }
            if i + 1 <= n {
                fib_is_monotonic((i + 1) as nat, n as nat);
            }
        }

        let temp = a;
        a = b;
        b = temp + b;
        i = i + 1;
    }

    b
}
// </vc-code>

}
fn main() {}