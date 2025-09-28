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
proof fn fib_step(n: nat)
    ensures fibonacci((n + 2) as nat) == fibonacci((n + 1) as nat) + fibonacci(n)
{
    // Since n is nat, n + 2 >= 2, so the recursive case applies
    assert(n + 2 != 0);
    assert(n + 2 != 1);
    assert(
        fibonacci((n + 2) as nat)
        ==
        if (n + 2) == 0 {
            0
        } else if (n + 2) == 1 {
            1
        } else {
            fibonacci((n + 1) as nat) + fibonacci(n)
        }
    );
    assert(fibonacci((n + 2) as nat) == fibonacci((n + 1) as nat) + fibonacci(n));
}
// </vc-helpers>

// <vc-spec>
fn fibonacci_iterative(n: u64) -> (f: u64)
    requires n < 100  // practical bound to prevent overflow
    ensures f == fibonacci(n as nat)
// </vc-spec>
// <vc-code>
{
    let mut i: u64 = 0;
    let mut prev: u64 = 0;
    let mut curr: u64 = 1;

    while i < n
        invariant
            i <= n,
            prev == fibonacci(i as nat),
            curr == fibonacci((i + 1) as nat)
        decreases (n - i) as nat
    {
        let next = prev + curr;

        proof {
            fib_step(i as nat);
            assert(fibonacci((i + 2) as nat) == fibonacci((i + 1) as nat) + fibonacci(i as nat));
            assert(next == prev + curr);
            assert(next == fibonacci((i + 1) as nat) + fibonacci(i as nat));
            assert(next == fibonacci((i + 2) as nat));
        }

        prev = curr;
        curr = next;
        i = i + 1;
    }
    assert(i == n);
    prev
}
// </vc-code>

fn main() {
}

}