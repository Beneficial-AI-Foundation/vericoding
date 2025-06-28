use builtin::*;
use builtin_macros::*;

verus! {

spec fn Fib(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        Fib((n - 1) as nat) + Fib((n - 2) as nat)
    }
}

fn ComputeFib(n: nat) -> (x: nat)
    ensures
        x == Fib(n)
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
                i >= 2,
                i <= n + 1,
                a == Fib((i - 2) as nat),
                b == Fib((i - 1) as nat)
        {
            let temp = a + b;
            a = b;
            b = temp;
            i = i + 1;
        }
        b
    }
}

fn main() {
}

}