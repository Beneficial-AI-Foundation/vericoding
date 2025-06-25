// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

fn gcdCalc(m: nat, n: nat) -> (res: nat)
    requires
        m>0 && n>0
    ensures
        res == gcd(m,n)
{
    return 0;
}

}