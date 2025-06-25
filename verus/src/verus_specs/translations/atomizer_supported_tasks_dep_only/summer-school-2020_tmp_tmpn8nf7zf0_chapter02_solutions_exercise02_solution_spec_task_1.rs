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
    &&& 1 < i
    &&& forall|f: nat| 1 < f < i ==> !divides(f, i)
}

// Convincing the proof to go through requires adding
// a loop invariant and a triggering assert.
// SPEC 

// Convincing the proof to go through requires adding
// a loop invariant and a triggering assert.
pub fn test_prime(i: nat) -> (result: bool)
    requires(1 < i)
    ensures(result == IsPrime(i))
{
}

//ATOM_PLACEHOLDER_Main

}