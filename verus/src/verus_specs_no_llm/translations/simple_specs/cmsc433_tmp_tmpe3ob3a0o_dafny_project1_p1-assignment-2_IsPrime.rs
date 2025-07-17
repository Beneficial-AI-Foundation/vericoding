// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_IsPrime(m: int) -> isPrime : bool
    requires
        m > 0 // m must be greater than 0
    ensures
        isPrime <==> (m > 1 && forall |j: int| 2 <= j < m ==> m % j != 0) 
	//,
        states that "isPrime is true iff m > 1 && not divisible by [2, m-1)"
;

proof fn lemma_IsPrime(m: int) -> (isPrime: bool)
    requires
        m > 0 // m must be greater than 0
    ensures
        isPrime <==> (m > 1 && forall |j: int| 2 <= j < m ==> m % j != 0) 
	//,
        states that "isPrime is true iff m > 1 && not divisible by [2, m-1)"
{
    false
}

}