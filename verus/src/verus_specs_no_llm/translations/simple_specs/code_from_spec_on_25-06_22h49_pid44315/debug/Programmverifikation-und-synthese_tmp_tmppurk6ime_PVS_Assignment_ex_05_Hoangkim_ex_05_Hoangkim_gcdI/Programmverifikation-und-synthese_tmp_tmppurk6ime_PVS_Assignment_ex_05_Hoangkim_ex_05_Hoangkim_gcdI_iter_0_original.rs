// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn gcdI(m: int, n: int) -> (g: int)
    requires
        m > 0 && n > 0
    ensures
        g == gcd(m, n)
{
    return 0;
}

}