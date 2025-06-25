use vstd::prelude::*;

verus! {

spec fn factorial(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { n * factorial((n - 1) as nat) }
}

pub fn additive_factorial(n: nat) -> (u: nat)
    ensures u == factorial(n)
{
}

pub fn find(A: &mut Vec<int>, N: int, f: int)
    requires 
        A.len() == N,
        0 <= f < N,
    ensures
        forall|p: int, q: int| 0 <= p <= f <= q < N ==> A[p] <= A[q]
{
}

}