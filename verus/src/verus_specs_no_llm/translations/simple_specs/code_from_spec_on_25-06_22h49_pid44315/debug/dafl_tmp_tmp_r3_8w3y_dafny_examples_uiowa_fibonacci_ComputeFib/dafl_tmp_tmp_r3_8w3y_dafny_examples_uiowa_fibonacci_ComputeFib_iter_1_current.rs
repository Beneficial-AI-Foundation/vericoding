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
        
        while i <= n
            invariant
                2 <= i <= n + 1,
                a == fib(i - 2),
                b == fib(i - 1)
        {
            let temp = a + b;
            a = b;
            b = temp;
            i = i + 1;
        }
        
        return b;
    }
}

fn main() {
}

}