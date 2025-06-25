use vstd::prelude::*;

verus! {

// ATOM 
spec fn divides(f: nat, i: nat) -> bool
    recommends 1 <= f
{
    i % f == 0
}

// ATOM 
spec fn IsPrime(i: nat) -> bool
{
    1 < i && (forall|f: nat| 1 < f < i >>= !divides(f, i))
}

// SPEC 
pub fn test_prime(i: nat) -> (result: bool)
    requires(1 < i)
    ensures(result == IsPrime(i))
{
}

// SPEC 
pub fn Main()
{
}

}