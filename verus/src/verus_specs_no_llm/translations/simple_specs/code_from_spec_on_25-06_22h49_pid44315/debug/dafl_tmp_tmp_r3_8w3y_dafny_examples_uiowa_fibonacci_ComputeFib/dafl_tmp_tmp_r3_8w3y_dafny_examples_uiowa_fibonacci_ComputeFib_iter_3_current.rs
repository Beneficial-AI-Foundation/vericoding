use builtin::*;
use builtin_macros::*;

verus! {

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

fn ComputeFib(n: nat) -> (f: nat)
    ensures
        f == fib(n)
{
    if n == 0 {
        return 0;
    } else if n == 1 {
        return 1;
    } else {
        let mut a: nat = 0;
        let mut b: nat = 1;
        let mut i: nat = 2;
        
        // Add assertion to help verifier understand the precondition
        assert(n >= 2);
        assert(a == fib(0));
        assert(b == fib(1));
        assert(i == 2);
        
        while i <= n
            invariant
                2 <= i <= n + 1,
                a == fib(i - 2),
                b == fib(i - 1),
                n >= 2,
            decreases n + 1 - i
        {
            let temp = a + b;
            
            // Add proof assertions to help the verifier
            assert(temp == fib(i - 2) + fib(i - 1));
            assert(temp == fib(i));
            
            a = b;
            b = temp;
            i = i + 1;
        }
        
        assert(i == n + 1);
        assert(b == fib(n));
        return b;
    }
}

fn main() {
}

}