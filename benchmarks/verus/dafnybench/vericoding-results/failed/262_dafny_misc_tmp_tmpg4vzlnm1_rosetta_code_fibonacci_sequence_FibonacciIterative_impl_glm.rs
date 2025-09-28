use vstd::prelude::*;

verus! {

// definition of Fibonacci numbers
spec fn fibonacci(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        fibonacci((n - 1) as nat) + fibonacci((n - 2) as nat)
    }
}

// iterative calculation of Fibonacci numbers

// <vc-helpers>
proof fn fibonacci_addition(i: nat)
    ensures fibonacci(i) == fibonacci((i - 1) as nat) + fibonacci((i - 2) as nat)
    decreases i
{
    if i >= 2 {
        fibonacci_addition((i - 1) as nat);
    }
}

proof fn fibonacci_monotonic(n: nat, m: nat)
    ensures n <= m ==> fibonacci(n) <= fibonacci(m)
    decreases m
{
    if n < m {
        if m == 0 || m == 1 {
        } else {
            fibonacci_monotonic(n, (m - 1) as nat);
            fibonacci_monotonic(n, (m - 2) as nat);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn fibonacci_iterative(n: u64) -> (f: u64)
    requires n < 100  // practical bound to prevent overflow
    ensures f == fibonacci(n as nat)
// </vc-spec>
// <vc-code>
{
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
                a == fibonacci((i - 2) as nat),
                b == fibonacci((i - 1) as nat),
                b >= a,
            decreases n - i
        {
            proof {
                fibonacci_addition(i as nat);
            }
            let c = a + b;
            assert(c == fibonacci(i as nat));
            a = b;
            b = c;
            proof {
                if i < n {
                    fibonacci_monotonic((i - 1) as nat, i as nat);
                }
            }
            i += 1;
        }
        b
    }
}
// </vc-code>

fn main() {
}

}