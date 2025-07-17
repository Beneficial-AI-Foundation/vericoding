// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_IsPrime(n: int) -> result: bool
    requires
        n >= 2
    ensures
        result <==> (forall |k: int| 2 <= k < n ==> n % k != 0)
;

proof fn lemma_IsPrime(n: int) -> (result: bool)
    requires
        n >= 2
    ensures
        result <==> (forall |k: int| 2 <= k < n ==> n % k != 0)
{
    false
}

}