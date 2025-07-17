// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn divides(f: nat, i: nat)
 requires 1<=f
{
 i % f == 0
}


//ATOM

predicate IsPrime(i:nat) -> bool {
    && 1<i
 && ( forall |f: int| 1 < f < i ==> !divides(f, i) )
}

}