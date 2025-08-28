use vstd::prelude::*;

verus! {

spec fn fib(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 }
    else if n == 1 { 1 }
    else { fib((n - 1) as nat) + fib((n - 2) as nat) }
}

// <vc-helpers>
proof fn lemma_fib_monotonic(i: nat, j: nat)
    requires i <= j
    ensures fib(i) <= fib(j)
    decreases j
{
    if i == j {
    } else if j == 0 {
    } else if j == 1 {
        if i == 0 {
        }
    } else {
        if i <= j - 1 {
            lemma_fib_monotonic(i, (j - 1) as nat);
        }
        if i <= j - 2 {
            lemma_fib_monotonic(i, (j - 2) as nat);
        }
    }
}

proof fn lemma_fib_bounds(n: nat)
    requires n < 100
    ensures fib(n) < 0x10000000000000000nat
    decreases n
{
    if n == 0 {
    } else if n == 1 {
    } else {
        lemma_fib_bounds((n - 1) as nat);
        lemma_fib_bounds((n - 2) as nat);
    }
}

proof fn lemma_fib_fits_u64(n: nat)
    requires n < 100
    ensures fib(n) <= 0xffffffffffffffffu64 as nat
{
    lemma_fib_bounds(n);
    assert(0x10000000000000000nat > 0xffffffffffffffffu64 as nat);
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn fibonacci1(n: u64) -> (f: u64)
    requires n < 100, // practical bound to prevent overflow
    ensures f == fib(n as nat)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    proof {
        lemma_fib_bounds(n as nat);
    }
    
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        let mut prev = 0u64;
        let mut curr = 1u64;
        let mut i = 2u64;
        
        while i <= n
            invariant 
                2 <= i <= n + 1,
                prev == fib((i - 2) as nat),
                curr == fib((i - 1) as nat),
                fib((i - 1) as nat) < 0x10000000000000000nat,
                fib((i - 2) as nat) < 0x10000000000000000nat,
                i <= 101,
                (i - 1) as nat < 100,
                (i - 2) as nat < 100
            decreases n - i
        {
            proof {
                lemma_fib_bounds((i - 1) as nat);
                lemma_fib_bounds((i - 2) as nat);
                lemma_fib_bounds(i as nat);
                lemma_fib_fits_u64((i - 1) as nat);
                lemma_fib_fits_u64((i - 2) as nat);
                lemma_fib_fits_u64(i as nat);
                assert(prev as nat + curr as nat == fib((i - 2) as nat) + fib((i - 1) as nat));
                assert(fib((i - 2) as nat) + fib((i - 1) as nat) == fib(i as nat));
                assert(fib(i as nat) < 0x10000000000000000nat);
            }
            let next = prev + curr;
            prev = curr;
            curr = next;
            i = i + 1;
        }
        
        curr
    }
}
// </vc-code>

fn main() {}

}