// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn divides(f: nat, i: nat)
  requires 1<=f
{
  i % f == 0
}


// ATOM 

predicate IsPrime(i:nat) -> bool {
    and 1 < i
  and forall|f: int| 1 < f < i ==> !divides(f, i)
}

}