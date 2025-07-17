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

spec fn spec_test_prime(i: nat) -> result:bool
    requires
        1<i
    ensures
        result == IsPrime(i)
;

proof fn lemma_test_prime(i: nat) -> (result: bool)
    requires
        1<i
    ensures
        result == IsPrime(i)
{
    false
}

}