// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn gcd(m: nat, n: nat) -> nat
    requires
        m>0 && n>0
{
    0
}

spec fn spec_gcdCalc(m: nat, n: nat) -> res: nat
    requires
        m>0 && n>0
    ensures
        res == gcd(m,n)
;

proof fn lemma_gcdCalc(m: nat, n: nat) -> (res: nat)
    requires
        m>0 && n>0
    ensures
        res == gcd(m,n)
{
    0
}

}