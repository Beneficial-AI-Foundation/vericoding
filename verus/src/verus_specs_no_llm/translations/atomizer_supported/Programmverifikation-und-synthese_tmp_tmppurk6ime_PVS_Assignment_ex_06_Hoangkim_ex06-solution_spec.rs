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

fn gcdI(m: int, n: int) -> (d: int)
    requires
        m > 0 && n > 0
    ensures
        d == gcd(m,n)
{
    return 0;
}

}