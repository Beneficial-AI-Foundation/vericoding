// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn gcdI(m: int, n: int) -> (d: int)
    requires m > 0 and n > 0
    ensures d == gcd(m,n)
{
}

}