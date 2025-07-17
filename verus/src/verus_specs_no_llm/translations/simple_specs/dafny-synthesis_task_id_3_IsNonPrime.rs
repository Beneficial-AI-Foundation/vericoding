// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_IsNonPrime(n: int) -> result: bool
    requires
        n >= 2
    ensures
        result <==> (exists |k: int| 2 <= k < n && n % k == 0)
;

proof fn lemma_IsNonPrime(n: int) -> (result: bool)
    requires
        n >= 2
    ensures
        result <==> (exists |k: int| 2 <= k < n && n % k == 0)
{
    false
}

}