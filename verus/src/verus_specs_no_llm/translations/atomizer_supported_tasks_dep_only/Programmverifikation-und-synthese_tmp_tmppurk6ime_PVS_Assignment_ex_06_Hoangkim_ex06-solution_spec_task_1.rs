// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_gcdI(m: int, n: int) -> d:int
    requires
        m > 0 && n > 0
    ensures
        d == gcd(m,n)
;

proof fn lemma_gcdI(m: int, n: int) -> (d: int)
    requires
        m > 0 && n > 0
    ensures
        d == gcd(m,n)
{
    0
}

}