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
proof fn lemma_fibonacci_step(n: nat)
    requires n >= 2
    ensures fibonacci(n) == fibonacci((n - 1) as nat) + fibonacci((n - 2) as nat)
{
}

proof fn lemma_fibonacci_invariant_update(i: nat, a: nat, b: nat)
    requires 
        i >= 1,
        a == fibonacci((i - 1) as nat),
        b == fibonacci(i as nat)
    ensures 
        b == fibonacci(i as nat),
        a + b == fibonacci((i + 1) as nat)
{
    if i >= 2 {
        lemma_fibonacci_step((i + 1) as nat);
        assert(fibonacci((i + 1) as nat) == fibonacci(i as nat) + fibonacci((i - 1) as nat));
    } else if i == 1 {
        assert(fibonacci(2) == fibonacci(1) + fibonacci(0));
        assert(fibonacci(2) == 1 + 0);
    }
}

proof fn lemma_fibonacci_bounded(n: nat)
    requires n < 100
    ensures fibonacci(n) <= u64::MAX
{
    if n <= 93 {
        assert(fibonacci(93) <= 12200160415121876738);
        assert(12200160415121876738 <= u64::MAX);
    }
}

proof fn lemma_fibonacci_overflow_safe(i: nat)
    requires i >= 1 && i < 99
    ensures fibonacci((i - 1) as nat) <= u64::MAX - fibonacci(i as nat)
{
    lemma_fibonacci_bounded((i - 1) as nat);
    lemma_fibonacci_bounded(i as nat);
    lemma_fibonacci_bounded((i + 1) as nat);
    assert(fibonacci((i - 1) as nat) + fibonacci(i as nat) == fibonacci((i + 1) as nat));
    assert(fibonacci((i + 1) as nat) <= u64::MAX);
    assert(fibonacci((i - 1) as nat) <= u64::MAX - fibonacci(i as nat));
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn fibonacci_iterative(n: u64) -> (f: u64)
    requires n < 100  // practical bound to prevent overflow
    ensures f == fibonacci(n as nat)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if n == 0 {
        return 0;
    }
    if n == 1 {
        return 1;
    }
    
    let mut a: u64 = 0;
    let mut b: u64 = 1;
    let mut i: u64 = 1;
    
    while i < n
        invariant
            i >= 1,
            i <= n,
            a == fibonacci((i - 1) as nat),
            b == fibonacci(i as nat),
            i < 99,
            i < n ==> a <= u64::MAX - b
        decreases n - i
    {
        proof {
            lemma_fibonacci_invariant_update(i as nat, a as nat, b as nat);
            lemma_fibonacci_overflow_safe(i as nat);
        }
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