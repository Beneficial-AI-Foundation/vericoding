use vstd::prelude::*;

verus! {

spec fn Fib(n: nat) -> nat {
    if n < 2 {
        n
    } else {
        Fib((n - 2) as nat) + Fib((n - 1) as nat)
    }
}

pub fn ComputeFib(n: nat) -> (x: nat)
    ensures x == Fib(n)
{
}

}