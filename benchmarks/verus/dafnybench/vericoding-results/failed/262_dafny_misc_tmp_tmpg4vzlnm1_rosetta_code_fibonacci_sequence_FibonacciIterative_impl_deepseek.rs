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
proof fn lemma_fibonacci_properties(n: nat)
    requires
        n < 100,
    ensures
        forall|k: nat| k <= n ==> #[trigger] fibonacci(k) <= 2 * k + 1,
    decreases n
{
    if n > 0 {
        lemma_fibonacci_properties((n - 1) as nat);
    }
    if n == 0 {
        assert(fibonacci(0) == 0);
        assert(fibonacci(0) <= 2 * 0 + 1);
    } else if n == 1 {
        assert(fibonacci(1) == 1);
        assert(fibonacci(1) <= 2 * 1 + 1);
    } else {
        lemma_fibonacci_properties((n - 1) as nat);
        assert(fibonacci(n) == fibonacci((n - 1) as nat) + fibonacci((n - 2) as nat));
        assert(fibonacci((n - 1) as nat) <= 2 * (n - 1) + 1);
        assert(fibonacci((n - 2) as nat) <= 2 * (n - 2) + 1);
        assert(fibonacci(n) <= (2 * (n - 1) + 1) + (2 * (n - 2) + 1));
        assert((2 * (n - 1) + 1) + (2 * (n - 2) + 1) == 4 * n - 3);
        if n >= 2 {
            assert(4 * n - 3 <= 2 * n + 1) by {
                assert(2 * n <= 4 * n - 3 + 1);
                assert(4 * n - 3 <= 2 * n + 1 ==> 2 * n <= 4);
                if n > 2 {
                    assert(2 * n + 1 == 2 * n + 1);
                    assert(4 * n - 3 - (2 * n + 1) == 2 * n - 4);
                    if n >= 2 {
                        assert(2 * n - 4 >= 0);
                    }
                }
            };
        }
        assert(fibonacci(n) <= 2 * n + 1);
    }
}

proof fn lemma_fibonacci_recurrence(k: nat)
    requires
        k >= 2,
    ensures
        fibonacci(k) == fibonacci((k - 1) as nat) + fibonacci((k - 2) as nat),
{
}

proof fn lemma_fibonacci_monotonic(i: nat, j: nat)
    requires
        i <= j,
    ensures
        fibonacci(i) <= fibonacci(j),
    decreases j - i
{
    if i < j {
        lemma_fibonacci_monotonic(i, (j - 1) as nat);
        if j >= 2 {
            lemma_fibonacci_recurrence(j);
        }
    }
}

proof fn lemma_fibonacci_bounds(i: nat)
    requires
        i < 100,
    ensures
        fibonacci(i) <= 2 * i + 1,
{
    lemma_fibonacci_properties(i);
}

proof fn lemma_fibonacci_non_negative(i: nat)
    ensures
        fibonacci(i) >= 0,
{
    if i == 0 {
    } else if i == 1 {
    } else if i >= 2 {
        lemma_fibonacci_non_negative((i - 1) as nat);
        lemma_fibonacci_non_negative((i - 2) as nat);
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
        return 0;
    }
    if n == 1 {
        return 1;
    }
    
    let mut a: u64 = 0;
    let mut b: u64 = 1;
    let mut i: u64 = 2;
    
    proof {
        assert(a == fibonacci(0)); 
        assert(b == fibonacci(1));
        lemma_fibonacci_bounds(0);
        lemma_fibonacci_bounds(1);
    }
    
    while i <= n
        invariant
            2 <= i && i <= n + 1,
            a == fibonacci((i - 2) as nat),
            b == fibonacci((i - 1) as nat),
            a <= 2 * (i - 2) + 1,
            b <= 2 * (i - 1) + 1,
        decreases n - i
    {
        proof {
            lemma_fibonacci_bounds((i - 2) as nat);
            lemma_fibonacci_bounds((i - 1) as nat);
            lemma_fibonacci_non_negative((i - 2) as nat);
            lemma_fibonacci_non_negative((i - 1) as nat);
        }
        
        let next: u64 = a + b;
        proof {
            lemma_fibonacci_recurrence(i as nat);
            assert(fibonacci(i as nat) == fibonacci((i - 1) as nat) + fibonacci((i - 2) as nat));
            assert(next == fibonacci(i as nat));
        }
        a = b;
        b = next;
        i = i + 1;
        
        proof {
            assert(a == fibonacci((i - 2) as nat));
            assert(b == fibonacci((i - 1) as nat));
            lemma_fibonacci_bounds((i - 2) as nat);
            lemma_fibonacci_bounds((i - 1) as nat);
        }
    }
    
    b
}
// </vc-code>

fn main() {
}

}