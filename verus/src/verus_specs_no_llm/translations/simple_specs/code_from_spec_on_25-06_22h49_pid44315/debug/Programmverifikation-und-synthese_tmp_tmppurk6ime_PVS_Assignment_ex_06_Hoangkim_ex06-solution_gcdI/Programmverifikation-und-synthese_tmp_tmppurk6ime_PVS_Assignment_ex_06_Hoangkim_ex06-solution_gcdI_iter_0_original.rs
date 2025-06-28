// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
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