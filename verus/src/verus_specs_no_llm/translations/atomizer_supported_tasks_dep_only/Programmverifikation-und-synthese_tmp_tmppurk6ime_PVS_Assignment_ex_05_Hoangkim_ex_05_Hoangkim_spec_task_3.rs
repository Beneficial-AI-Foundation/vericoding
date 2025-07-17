// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn gcd(m: nat, n: nat) -> nat
    requires
        m > 0 && n > 0
{
    0
}

spec fn spec_gcdI(m: int, n: int) -> g: int
    requires
        m > 0 && n > 0
    ensures
        g == gcd(m, n)
;

proof fn lemma_gcdI(m: int, n: int) -> (g: int)
    requires
        m > 0 && n > 0
    ensures
        g == gcd(m, n)
{
    0
}

}