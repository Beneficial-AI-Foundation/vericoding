use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Spec function to define Fibonacci sequence
spec fn Fib(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        Fib(n - 1) + Fib(n - 2)
    }
}

fn ComputeFib(n: nat) -> (x: nat)
    ensures x == Fib(n)
{
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        let mut a: nat = 0;
        let mut b: nat = 1;
        let mut i: nat = 2;
        
        while i <= n
            invariant
                2 <= i <= n + 1,
                a == Fib(i - 2),
                b == Fib(i - 1),
        {
            let temp = a + b;
            a = b;
            b = temp;
            i = i + 1;
        }
        
        // When the loop exits, i == n + 1
        // So we have a == Fib((n + 1) - 2) == Fib(n - 1)
        // and b == Fib((n + 1) - 1) == Fib(n)
        assert(i == n + 1);
        assert(b == Fib(n));
        b
    }
}

fn Teste() -> (result: nat)
    ensures result == Fib(0)
{
    0
}

}