use vstd::prelude::*;

verus! {

spec fn fib(n: nat) -> nat {
    if n < 2 { n } else { fib((n-2) as nat) + fib((n-1) as nat) }
}

pub fn fibIter(n: nat) -> (a: nat)
    requires n > 0
    ensures a == fib(n)
{
    todo!()
}

}