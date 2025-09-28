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
//
// </vc-helpers>

// <vc-spec>
fn fibonacci_iterative(n: u64) -> (f: u64)
    requires n < 100  // practical bound to prevent overflow
    ensures f == fibonacci(n as nat)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        return 0;
    }
    if n == 1 {
        return 1;
    }
    let mut i: u64 = 0;
    let mut a: u64 = 0;
    let mut b: u64 = 1;
    while i < n - 1
        invariant
            i <= (n as int - 1),
            a == fibonacci(i as nat),
            b == fibonacci((i as nat) + 1),
        decreases (n as int - i as int)
    {
        let temp = a + b;
        a = b;
        b = temp;
        i = i + 1;
    }
    b
}
// </vc-code>

fn main() {
}

}