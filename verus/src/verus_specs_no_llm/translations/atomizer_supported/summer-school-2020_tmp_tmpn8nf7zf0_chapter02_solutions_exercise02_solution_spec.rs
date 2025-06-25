// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

spec fn divides(f: nat, i: nat)
  requires 1<=f
{
  i % f == 0
}


// ATOM 

predicate IsPrime(i:nat) -> bool {
    && 1<i
  && ( forall f :: 1 < f < i ==> !divides(f, i) )
}

fn test_prime(i: nat) -> (result: bool)
    requires
        1<i
    ensures
        result == IsPrime(i)
{
    return false;
}

}