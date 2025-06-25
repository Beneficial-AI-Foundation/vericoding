// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn gcdCalc(m: nat, n: nat) -> (res: nat)
    requires m>0 and n>0;
    ensures res == gcd(m,n);
{
}

}