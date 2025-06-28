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
        let mut a: nat = 0;
        let mut b: nat = 1;
        let mut i: nat = 2;
        
        while i <= n
            invariant
                2 <= i <= n + 1,
                a == fib(i - 2),
                b == fib(i - 1)
            decreases n + 1 - i
        {
            let temp = a + b;
            
            proof {
                // Help Verus understand that temp equals fib(i)
                assert(i >= 2);
                assert(fib(i) == fib(i - 1) + fib(i - 2)) by {
                    reveal_with_fuel(fib, 3);
                };
                assert(temp == fib(i));
            }
            
            a = b;
            b = temp;
            i = i + 1;
        }
        
        b
    }
}

}