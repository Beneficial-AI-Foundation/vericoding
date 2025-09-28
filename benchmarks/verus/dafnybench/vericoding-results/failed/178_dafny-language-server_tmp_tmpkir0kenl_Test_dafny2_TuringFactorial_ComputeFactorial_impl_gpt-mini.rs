use vstd::prelude::*;

verus! {

spec fn factorial(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { n * factorial((n - 1) as nat) }
}

// <vc-helpers>
// Added helper lemma to justify factorial succ step
proof fn factorial_succ(m: nat)
    ensures factorial(m + 1) == (m + 1) * factorial(m)
    decreases m
{
    if m == 0 {
        // factorial(1) == 1 and factorial(0) == 1 by definition of factorial
        assert(factorial(1) == 1);
        assert(factorial(0) == 1);
    } else {
        factorial_succ(m - 1);
        // The equality follows by the definition of factorial
    }
}
// </vc-helpers>

// <vc-spec>
fn compute_factorial(n: i32) -> (u: i32)
    requires 1 <= n,
    ensures u == factorial(n as nat),
// </vc-spec>
// <vc-code>
{
    let mut i: i32 = 1;
    let mut acc: i32 = 1;
    while i < n
        invariant { 1 <= i && i <= n }
        invariant { (acc as nat) == factorial(i as nat) }
        decreases { (n - i) as nat }
    {
        let next: i32 = i + 1;
        let new_acc: i32 = acc * next;
        proof {
            assert((acc as nat) == factorial(i as nat));
            // Use helper to show factorial(next) = next * factorial(i)
            factorial_succ(i as nat);
            assert(factorial((next as nat)) == (next as nat) * factorial(i as nat));
            assert((new_acc as nat) == (acc as nat) * (next as nat));
            assert((new_acc as nat) == factorial(next as nat));
        }
        acc = new_acc;
        i = next;
    }
    proof {
        assert(!(i < n));
        assert(i >= n);
        assert(i <= n);
        assert(i == n);
        assert((acc as nat) == factorial(i as nat));
    }
    acc
}
// </vc-code>

fn main() {
}

}