use vstd::prelude::*;

verus! {

// recursive definition of factorial
spec fn factorial(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { n * factorial((n - 1) as nat) }
}

// iterative implementation of factorial

// <vc-helpers>
proof fn lemma_factorial_iterative(n: nat, i: nat, acc: nat)
    requires
        i <= n,
        acc == factorial(n - i),
    ensures
        acc * factorial(i) == factorial(n),
    decreases i
{
    if i == 0 {
        assert(acc == factorial(n));
    } else {
        lemma_factorial_iterative(n, i - 1, acc * i);
        assert(acc * i * factorial(i - 1) == factorial(n));
        assert(factorial(i) == i * factorial(i - 1));
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn iterative_factorial(n: u32) -> (result: u32)
    requires n < 13, // prevent overflow
    ensures result == factorial(n as nat)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn iterative_factorial(n: u32) -> (result: u32)
    requires n < 13,
    ensures result == factorial(n as nat)
{
    let mut acc: u32 = 1;
    let mut i: u32 = 1;
    
    while i <= n
        invariant
            i <= n + 1,
            acc == factorial((n - i + 1) as nat),
    {
        acc = acc * i;
        i = i + 1;
    }
    
    proof {
        lemma_factorial_iterative(n as nat, (n - i + 1) as nat, acc as nat);
    }
    
    acc
}
// </vc-code>

fn main() {}

}