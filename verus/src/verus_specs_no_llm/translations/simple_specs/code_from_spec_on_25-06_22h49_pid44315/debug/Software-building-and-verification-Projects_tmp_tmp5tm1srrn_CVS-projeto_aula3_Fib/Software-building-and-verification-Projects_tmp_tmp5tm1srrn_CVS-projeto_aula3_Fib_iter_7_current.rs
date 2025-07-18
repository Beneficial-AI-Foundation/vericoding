use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

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

fn Fib(n: nat) -> (r: nat)
    ensures
        r == fib(n)
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
                b == fib(i - 1),
        {
            let temp = a + b;
            // Add proof assertion to help verification
            assert(temp == fib(i - 2) + fib(i - 1));
            assert(temp == fib(i));
            a = b;
            b = temp;
            i = i + 1;
        }
        
        // At this point, i == n + 1, so b == fib((n + 1) - 1) == fib(n)
        assert(i == n + 1);
        assert(b == fib(i - 1));
        assert(b == fib(n));
        b
    }
}

}