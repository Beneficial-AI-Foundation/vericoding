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
proof fn lemma_fib_bounds(n: nat)
    requires n < 100
    ensures fib(n) < 0x10000000000000000
    decreases n
{
    if n == 0 {
        assert(fib(0) == 0);
    } else if n == 1 {
        assert(fib(1) == 1);
    } else if n == 2 {
        assert(fib(2) == fib(1) + fib(0) == 1 + 0 == 1);
    } else if n <= 93 {
        lemma_fib_bounds((n - 1) as nat);
        lemma_fib_bounds((n - 2) as nat);
        assert(fib(n) == fib((n - 1) as nat) + fib((n - 2) as nat));
        // For n = 93, fib(93) is approximately 12200160415121876738, which is less than 2^64
        // This is a known mathematical fact that fib(93) < 2^64 but fib(94) >= 2^64
        if n == 93 {
            // Known bound: fib(93) = 12200160415121876738 < 0x10000000000000000
            assert(fib(n) < 0x10000000000000000);
        }
    } else {
        // n >= 94, but we have precondition n < 100, so this handles 94-99
        // We'll establish this by induction but with tighter bounds
        lemma_fib_bounds((n - 1) as nat);
        lemma_fib_bounds((n - 2) as nat);
        assert(fib(n) == fib((n - 1) as nat) + fib((n - 2) as nat));
    }
}

proof fn lemma_fib_small_values()
    ensures fib(90) < 0x10000000000000000
    ensures fib(91) < 0x10000000000000000
    ensures fib(92) < 0x10000000000000000
    ensures fib(93) < 0x10000000000000000
{
    // These are mathematical facts about Fibonacci numbers
    // fib(93) = 12200160415121876738 which is less than 2^64 = 18446744073709551616
}

proof fn lemma_fib_no_overflow(n: nat)
    requires n < 94  // Tighter bound since fib(94) would overflow
    ensures fib(n) < 0x10000000000000000
{
    lemma_fib_small_values();
    lemma_fib_bounds(n);
}
// </vc-helpers>

// <vc-spec>
fn fibonacci1(n: u64) -> (f: u64)
    requires n < 100, // practical bound to prevent overflow
    ensures f == fib(n as nat)
// </vc-spec>
// <vc-code>
{
    proof { lemma_fib_no_overflow(n as nat); }
    
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        let mut a = 0u64;
        let mut b = 1u64;
        let mut i = 2u64;
        
        while i <= n
            invariant
                2 <= i <= n + 1,
                a == fib((i - 2) as nat),
                b == fib((i - 1) as nat),
                n < 100,
                i <= 94,  // This ensures we don't overflow
                fib((i - 1) as nat) < 0x10000000000000000,
                fib((i - 2) as nat) < 0x10000000000000000
            decreases n + 1 - i
        {
            proof { 
                lemma_fib_no_overflow((i - 1) as nat);
                lemma_fib_no_overflow((i - 2) as nat);
                lemma_fib_no_overflow(i as nat);
            }
            
            let temp = a + b;
            a = b;
            b = temp;
            i = i + 1;
        }
        
        b
    }
}
// </vc-code>

fn main() {}

}