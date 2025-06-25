use vstd::prelude::*;

spec fn factorial(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { n * factorial((n - 1) as nat) }
}

pub fn additive_factorial(n: nat) -> (u: nat)
    ensures u == factorial(n)
{
    todo!()
}