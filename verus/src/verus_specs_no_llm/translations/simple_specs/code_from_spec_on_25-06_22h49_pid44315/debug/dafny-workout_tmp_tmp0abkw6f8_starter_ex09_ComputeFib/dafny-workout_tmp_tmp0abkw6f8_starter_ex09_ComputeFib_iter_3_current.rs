use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Spec function defining Fibonacci sequence
spec fn fib(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        fib(n - 1) + fib(n - 2)
    }
}

fn ComputeFib(n: nat) -> (b: nat)
    ensures
        b == fib(n)
{
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        let mut a = 0;
        let mut b = 1;
        let mut i = 2;
        
        while i <= n
            invariant
                2 <= i <= n + 1,
                a == fib((i - 2) as nat),
                b == fib((i - 1) as nat)
        {
            let temp = a + b;
            proof {
                // Help Verus understand that temp equals fib(i)
                assert(temp == a + b);
                assert(a == fib((i - 2) as nat));
                assert(b == fib((i - 1) as nat));
                assert(fib(i as nat) == fib((i - 1) as nat) + fib((i - 2) as nat));
                assert(temp == fib(i as nat));
            }
            a = b;
            b = temp;
            i = i + 1;
        }
        
        proof {
            // After the loop, i == n + 1, so we computed fib(n)
            assert(i == n + 1);
            assert(b == fib((i - 1) as nat));
            assert((i - 1) as nat == n);
        }
        
        b
    }
}

}